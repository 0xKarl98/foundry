//! Local, single-member Tempo consensus certificates.
//!
//! This is a deterministic development signer, not a running Simplex consensus network. It deals a
//! real 1-of-1 BLS12-381 sharing, and every locally mined non-genesis block immediately receives a
//! recoverable finalization certificate. It does not model notarizations, failed proposals, skipped
//! views, or multi-member DKG ceremonies. Rotations create entirely new group and proposer keys;
//! they are not resharings of an existing group key.
//!
//! With configured nonzero epoch length `L`, height `h` uses epoch `h / L`, view `h % L + 1`, and
//! parent view `h % L`. A boundary at `h % L == L - 1` publishes the native [`OnchainDkgOutcome`]
//! for the next epoch, including its scheduled replacement key. The complete [`TempoHeader`] is
//! hashed only after consensus context and this outcome have been installed. Context is omitted
//! before T4 and for genesis, following TIP-1031. Anvil keeps `sharedGasLimit` and
//! `timestampMillisPart` at zero; certificates authenticate the resulting local header, not a
//! production block-building policy.
//!
//! The wire adapter follows Tempo revision `2c25f7cd` and Commonware `2026.9.0`: native
//! finalization bytes are three unsigned varints, the 32-byte digest, and two 48-byte signatures.
//! The vote signs the proposal in `TEMPO_FINALIZE`; the seed signs the round in `TEMPO_SEED`. The
//! pinned Tempo implementation has one codec without historical format dispatch. `WireFormat`
//! records the corresponding local hardfork mapping and forces review when supported forks change.
//! Compatibility with this pinned decoder is not an upstream stability promise, nor a claim about
//! every historical node release. Future changes require the protocol confirmation tracked in
//! OSS-1186.
//!
//! The default seed is Keccak-256 of `anvil/tempo-consensus/` followed by the account mnemonic.
//! Committee entropy is Keccak-256 of the seed followed by an eight-byte big-endian counter.
//! Counter zero generates the initial committee; each accepted rotation increments it once. A
//! single ChaCha20 stream generates the ed25519 proposer before dealing the BLS sharing, preserving
//! the original spike's development identities.
//!
//! Rotation takes effect after the epoch containing the next block. Repeating it with the same
//! target epoch replaces the pending key while consuming another counter. A call at an already
//! mined epoch boundary schedules a later epoch and preserves the committee that boundary
//! announced. The identity RPC reports the committee used by the current locally mined epoch; the
//! rotation RPC reports the scheduled replacement.
//!
//! Snapshot/revert preserves the entire controller, including pending rotations made after the
//! latest block, certificates, and the derivation counter. Rollback/reorg instead restores the key
//! checkpoint of the retained mined height and deletes later certificates; rotations made after
//! that checkpoint are discarded. Replacement blocks receive new certificates, so a development
//! rewind can produce two independently valid certificates for different hashes at the same height.
//! Reset, or loading a different canonical history, clears certificates and rotations and restarts
//! the original seed-derived committee. State dumps do not import committee secrets or
//! certificates. Latest queries retain one complete block independently of archive pruning, as in
//! Tempo's consensus feed. Rewinding to an older pruned body can still return missing-content 503;
//! the cache does not restore discarded history.
//!
//! Fork history queries at or below the fork block are served by the upstream consensus RPC. Before
//! local mining, latest queries also use upstream; thereafter they use the newest local
//! certificate. A root certificate must match the pinned fork hash, even if upstream rewinds. The
//! local committee is an independent trust anchor and does not inherit upstream
//! committee trust or continuous views. Fork state and `eth_getProof` retain Anvil's existing
//! partial-trie limitations; this feature does not turn local certificates into authenticated
//! upstream state proofs.

use alloy_consensus::BlockHeader;
use alloy_primitives::{B256, Bytes, keccak256};
use anvil_core::eth::block::Block;
use commonware_codec::{Encode, Write, varint::UInt};
use commonware_cryptography::{
    Signer,
    bls12381::{
        dkg::feldman_desmedt::{self, Output},
        primitives::{group::Share, ops::threshold, sharing::Mode, variant::MinSig},
    },
    ed25519::{PrivateKey, PublicKey},
};
use commonware_math::algebra::Random;
use commonware_parallel::Sequential;
use commonware_utils::{N3f1, TryFromIterator, ordered};
use rand_chacha::{ChaCha20Rng, rand_core::SeedableRng};
use serde::{Deserialize, Serialize};
use std::{collections::BTreeMap, num::NonZeroU64, sync::Arc};
use tempo_dkg_onchain_artifacts::OnchainDkgOutcome;
use tempo_hardfork::TempoHardfork;
use tempo_primitives::{TempoConsensusContext, TempoHeader};

/// A local single-member committee, its scheduled replacements, and mined certificates.
#[derive(Clone)]
pub struct TempoConsensus {
    seed: B256,
    epoch_length: NonZeroU64,
    initial: TempoConsensusCheckpoint,
    state: TempoConsensusCheckpoint,
    checkpoints: BTreeMap<u64, TempoConsensusCheckpoint>,
    finalizations: BTreeMap<u64, TempoFinalization>,
    latest_block: Option<Arc<Block>>,
}

impl TempoConsensus {
    /// Creates a deterministic development committee with one participant and quorum one.
    pub fn new(seed: B256, epoch_length: NonZeroU64) -> Self {
        let initial = TempoConsensusCheckpoint {
            counter: 0,
            epoch: 0,
            committees: BTreeMap::from([(0, Arc::new(Committee::derive(seed, 0)))]),
        };
        Self {
            seed,
            epoch_length,
            initial: initial.clone(),
            state: initial,
            checkpoints: BTreeMap::new(),
            finalizations: BTreeMap::new(),
            latest_block: None,
        }
    }

    /// Derives the default consensus seed from the configured account mnemonic.
    pub fn default_seed(mnemonic: &str) -> B256 {
        let mut input = b"anvil/tempo-consensus/".to_vec();
        input.extend_from_slice(mnemonic.as_bytes());
        keccak256(input)
    }

    /// Returns the identity currently used for local blocks.
    pub fn identity(&self) -> TempoConsensusIdentity {
        self.identity_at(self.state.epoch)
    }

    /// Schedules a fresh committee after the epoch containing the next block.
    ///
    /// Repeated requests for the same epoch replace that pending committee. Committees already
    /// announced by a mined boundary remain scheduled, including when the current head is a
    /// boundary.
    pub fn rotate(&mut self, head: u64) -> Result<TempoConsensusIdentity, TempoConsensusError> {
        let next_height = head.checked_add(1).ok_or(TempoConsensusError::HeightOverflow)?;
        let from_epoch = (next_height / self.epoch_length.get())
            .checked_add(1)
            .ok_or(TempoConsensusError::EpochOverflow)?;
        let counter =
            self.state.counter.checked_add(1).ok_or(TempoConsensusError::CounterOverflow)?;
        let committee = Arc::new(Committee::derive(self.seed, counter));
        self.state.committees.insert(from_epoch, committee);
        self.state.counter = counter;
        Ok(self.identity_at(from_epoch))
    }

    /// Adds consensus metadata and the next epoch's DKG outcome before the header is hashed.
    ///
    /// Genesis and pre-T4 headers omit consensus context, following TIP-1031. Pre-T4 certificates
    /// still sign the historical header encoding. A terminal epoch that cannot announce its
    /// successor fails without changing the header or identity state.
    pub fn prepare_header(
        &self,
        header: &mut TempoHeader,
        hardfork: TempoHardfork,
    ) -> Result<(), TempoConsensusError> {
        let height = header.inner.number;
        if height == 0 {
            header.consensus_context = None;
            return Ok(());
        }
        let epoch = height / self.epoch_length.get();
        let parent_view = height % self.epoch_length.get();
        let outcome = if parent_view == self.epoch_length.get() - 1 {
            let next_epoch = epoch.checked_add(1).ok_or(TempoConsensusError::EpochOverflow)?;
            let committee = self.committee_at(next_epoch).1;
            Some(OnchainDkgOutcome {
                epoch: next_epoch,
                output: committee.output.clone(),
                next_players: committee.output.players().clone(),
                is_next_full_dkg: false,
            })
        } else {
            None
        };
        let proposer = B256::from(<[u8; 32]>::from(&self.committee_at(epoch).1.proposer))
            .try_into()
            .expect("the committee proposer is a valid ed25519 public key");
        header.consensus_context = hardfork.is_t4().then_some(TempoConsensusContext {
            epoch,
            view: parent_view + 1,
            parent_view,
            proposer,
        });
        if let Some(outcome) = outcome {
            header.inner.extra_data = match WireFormat::for_hardfork(hardfork) {
                WireFormat::Commonware202609 => outcome.encode().into(),
            };
        }
        Ok(())
    }

    /// Signs the final, stored header digest and checkpoints consensus state at this height.
    ///
    /// The caller must first prepare and hash the non-genesis Tempo header. Retain the latest
    /// complete block independently of archive pruning, matching Tempo's consensus feed.
    pub fn finalize(
        &mut self,
        block: &Block,
        hash: B256,
        hardfork: TempoHardfork,
    ) -> TempoFinalization {
        let height = block.header.number();
        assert_ne!(height, 0, "genesis has no local finalization certificate");
        let epoch = height / self.epoch_length.get();
        let parent_view = height % self.epoch_length.get();
        let view = parent_view + 1;
        let committee = self.committee_at(epoch).1;

        let certificate = match WireFormat::for_hardfork(hardfork) {
            WireFormat::Commonware202609 => {
                // Commonware Round and Proposal use unsigned varints followed by the raw digest.
                let mut round = Vec::new();
                UInt(epoch).write(&mut round);
                UInt(view).write(&mut round);
                let mut proposal = round.clone();
                UInt(parent_view).write(&mut proposal);
                proposal.extend_from_slice(hash.as_slice());

                let vote = threshold::sign_message::<MinSig>(
                    &committee.share,
                    b"TEMPO_FINALIZE",
                    &proposal,
                );
                let seed =
                    threshold::sign_message::<MinSig>(&committee.share, b"TEMPO_SEED", &round);
                let vote = threshold::recover::<MinSig, _>(
                    committee.output.public(),
                    [&vote],
                    &Sequential,
                )
                .expect("one valid partial signature satisfies a 1-of-1 sharing");
                let seed = threshold::recover::<MinSig, _>(
                    committee.output.public(),
                    [&seed],
                    &Sequential,
                )
                .expect("one valid partial signature satisfies a 1-of-1 sharing");

                // Native Finalization writes Proposal then its fixed-size vote and seed signatures.
                // The VRF certificate's Lazy wrapper adds neither a tag nor a length prefix.
                vote.write(&mut proposal);
                seed.write(&mut proposal);
                proposal.into()
            }
        };
        let finalization = TempoFinalization { epoch, view, digest: hash, certificate };
        self.state.epoch = epoch;
        self.finalizations.insert(height, finalization.clone());
        self.checkpoints.insert(height, self.state.clone());
        self.latest_block = Some(Arc::new(block.clone()));
        finalization
    }

    /// Returns a certificate for a locally mined height, excluding genesis.
    pub fn finalization(&self, height: u64) -> Option<&TempoFinalization> {
        self.finalizations.get(&height)
    }

    /// Returns the latest locally mined height and its certificate.
    pub fn latest(&self) -> Option<(u64, &TempoFinalization)> {
        self.finalizations.last_key_value().map(|(&height, certificate)| (height, certificate))
    }

    /// Removes unwound certificates and restores the key schedule and counter of the retained head.
    pub fn unwind(&mut self, height: u64) {
        self.state = self
            .checkpoints
            .range(..=height)
            .next_back()
            .map_or_else(|| self.initial.clone(), |(_, checkpoint)| checkpoint.clone());
        self.checkpoints.retain(|&number, _| number <= height);
        self.finalizations.retain(|&number, _| number <= height);
        if self.latest_block.as_ref().is_some_and(|block| block.header.number() > height) {
            self.latest_block = None;
        }
    }

    /// Clears certificates and rotations, restoring the original deterministic identity.
    pub fn reset(&mut self) {
        self.state = self.initial.clone();
        self.checkpoints.clear();
        self.finalizations.clear();
        self.latest_block = None;
    }

    fn identity_at(&self, epoch: u64) -> TempoConsensusIdentity {
        let (&from_epoch, committee) = self.committee_at(epoch);
        TempoConsensusIdentity {
            identity: committee.output.public().public().encode().into(),
            proposer: B256::from(<[u8; 32]>::from(&committee.proposer)),
            from_epoch,
            epoch_length: self.epoch_length.get(),
            participants: 1,
            quorum: committee.output.quorum::<N3f1>(),
        }
    }

    fn committee_at(&self, epoch: u64) -> (&u64, &Arc<Committee>) {
        self.state
            .committees
            .range(..=epoch)
            .next_back()
            .expect("epoch zero always has a committee")
    }

    /// Returns the complete latest block even when its archived transactions have been pruned.
    pub fn latest_block(&self) -> Option<&Block> {
        self.latest_block.as_deref()
    }
}

/// The public development committee returned by Anvil's identity RPCs.
#[derive(Clone, Debug, Deserialize, Serialize, PartialEq, Eq)]
#[serde(rename_all = "camelCase")]
pub struct TempoConsensusIdentity {
    /// Compressed 96-byte BLS12-381 G2 public key, encoded as a `0x`-prefixed hex string.
    pub identity: Bytes,
    /// The committee's ed25519 proposer key.
    pub proposer: B256,
    /// The first epoch using this identity.
    pub from_epoch: u64,
    /// Number of block heights per epoch.
    pub epoch_length: u64,
    /// Number of committee members.
    pub participants: u32,
    /// Number of shares required to sign a certificate.
    pub quorum: u32,
}

/// Certificate data bound to a locally mined Tempo header.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TempoFinalization {
    /// The proposal's epoch.
    pub epoch: u64,
    /// The proposal's view.
    pub view: u64,
    /// Hash of the complete RLP-encoded Tempo header.
    pub digest: B256,
    /// Complete native Simplex finalization bytes without extra framing.
    pub certificate: Bytes,
}

/// Key state at a mined height.
#[derive(Clone)]
struct TempoConsensusCheckpoint {
    counter: u64,
    epoch: u64,
    committees: BTreeMap<u64, Arc<Committee>>,
}

/// A rotation or epoch boundary cannot be represented.
#[derive(Clone, Copy, Debug, PartialEq, Eq, thiserror::Error)]
pub enum TempoConsensusError {
    /// The head has no representable successor.
    #[error("Tempo consensus block height overflow")]
    HeightOverflow,
    /// The next epoch cannot be represented.
    #[error("Tempo consensus epoch overflow")]
    EpochOverflow,
    /// All development key derivation counters have been exhausted.
    #[error("Tempo consensus identity counter overflow")]
    CounterOverflow,
}

struct Committee {
    proposer: PublicKey,
    output: Output<MinSig, PublicKey>,
    share: Share,
}

impl Committee {
    fn derive(seed: B256, counter: u64) -> Self {
        // Preserve the spike's development identity derivation: an eight-byte big-endian counter,
        // starting at zero, followed by ed25519 generation and dealing from the same ChaCha20
        // stream.
        let mut input = seed.to_vec();
        input.extend_from_slice(&counter.to_be_bytes());
        let mut rng = ChaCha20Rng::from_seed(keccak256(input).0);
        let proposer = PrivateKey::random(&mut rng).public_key();
        let players = ordered::Set::try_from_iter([proposer.clone()]).expect("one distinct player");
        let (output, shares) =
            feldman_desmedt::deal::<MinSig, _, N3f1>(&mut rng, Mode::NonZeroCounter, players)
                .expect("dealing to one player cannot fail");
        let share = shares.values()[0].clone();
        Self { proposer, output, share }
    }
}

/// The pinned Tempo revision uses one Commonware codec, without historical format dispatch.
/// This local emulation mapping is not an upstream promise about historical or future releases.
enum WireFormat {
    Commonware202609,
}

impl WireFormat {
    /// Exhaustive selection forces protocol review when a new Tempo hardfork is introduced.
    fn for_hardfork(hardfork: TempoHardfork) -> Self {
        // TempoHardfork is non-exhaustive, so additions must also invalidate this const assertion.
        const { assert!(TempoHardfork::VARIANTS.len() == 19) };
        match hardfork {
            TempoHardfork::Genesis
            | TempoHardfork::T0
            | TempoHardfork::T1
            | TempoHardfork::T1A
            | TempoHardfork::T1B
            | TempoHardfork::T1C
            | TempoHardfork::T2
            | TempoHardfork::T3
            | TempoHardfork::T4
            | TempoHardfork::T5
            | TempoHardfork::T6
            | TempoHardfork::T7
            | TempoHardfork::T8
            | TempoHardfork::T9
            | TempoHardfork::T10
            | TempoHardfork::T11
            | TempoHardfork::T12
            | TempoHardfork::T13
            | TempoHardfork::T14 => Self::Commonware202609,
            _ => unreachable!("all pinned Tempo hardforks are enumerated above"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloy_consensus::Sealable;
    use commonware_codec::DecodeExt;

    #[test]
    fn reproducible_identity_and_rotation() {
        let mut first = TempoConsensus::new(B256::ZERO, NonZeroU64::new(3).unwrap());
        let mut second = TempoConsensus::new(B256::ZERO, NonZeroU64::new(3).unwrap());
        assert_eq!(first.identity(), second.identity());
        assert_eq!(first.identity().identity.len(), 96);
        let rotated = first.rotate(0).unwrap();
        assert_ne!(rotated.identity, first.identity().identity);
        assert_eq!(rotated, second.rotate(0).unwrap());
        assert_eq!(rotated.from_epoch, 1);
        assert_eq!((rotated.participants, rotated.quorum), (1, 1));
    }

    #[test]
    fn boundary_rotation_preserves_already_announced_committee() {
        let mut consensus = TempoConsensus::new(B256::ZERO, NonZeroU64::new(3).unwrap());
        let original = consensus.identity();
        mine(&mut consensus, 1);
        let first = consensus.rotate(1).unwrap();
        let boundary = mine(&mut consensus, 2);
        let outcome = OnchainDkgOutcome::decode(boundary.inner.extra_data.as_ref()).unwrap();
        assert_eq!(outcome.epoch, 1);
        assert_eq!(outcome.network_identity().encode().as_ref(), first.identity.as_ref());
        assert_eq!(outcome.output.quorum::<N3f1>(), 1);
        assert_eq!(outcome.output.public().required(), 1);
        assert_eq!(outcome.next_players, outcome.output.players().clone());
        assert!(!outcome.is_next_full_dkg);
        assert_eq!(B256::from(boundary.consensus_context.unwrap().proposer), original.proposer);

        let replaced = consensus.rotate(2).unwrap();
        let second = consensus.rotate(2).unwrap();
        assert_eq!(second.from_epoch, 2);
        assert_ne!(second.identity, replaced.identity);
        assert_eq!(consensus.identity(), original);
        mine(&mut consensus, 3);
        assert_eq!(consensus.identity(), first);
        mine(&mut consensus, 4);
        let boundary = mine(&mut consensus, 5);
        let outcome = OnchainDkgOutcome::decode(boundary.inner.extra_data.as_ref()).unwrap();
        assert_eq!(outcome.epoch, 2);
        assert_eq!(outcome.network_identity().encode().as_ref(), second.identity.as_ref());
        assert_eq!(consensus.identity(), first);
        mine(&mut consensus, 6);
        assert_eq!(consensus.identity(), second);
    }

    #[test]
    fn unwind_restores_key_schedule_and_derivation_counter() {
        let mut consensus = TempoConsensus::new(B256::ZERO, NonZeroU64::new(3).unwrap());
        let original = consensus.identity();
        mine(&mut consensus, 1);
        let first = consensus.rotate(1).unwrap();
        mine(&mut consensus, 2);
        let old = mine(&mut consensus, 3).hash_slow();
        consensus.rotate(3).unwrap();
        consensus.unwind(1);
        assert_eq!(consensus.identity(), original);
        assert_eq!(consensus.latest().unwrap().0, 1);
        assert!(consensus.finalization(2).is_none());
        assert!(consensus.finalization(3).is_none());
        assert_eq!(consensus.rotate(1).unwrap(), first);
        mine(&mut consensus, 2);
        let mut replacement = TempoHeader::default();
        replacement.inner.number = 3;
        replacement.inner.timestamp = 42;
        consensus.prepare_header(&mut replacement, TempoHardfork::T4).unwrap();
        let block = Block::new(replacement.clone().into(), Default::default());
        let certificate = consensus.finalize(&block, replacement.hash_slow(), TempoHardfork::T4);
        assert_ne!(certificate.digest, old);
        assert_eq!(certificate.digest, replacement.hash_slow());
        assert_eq!(consensus.identity(), first);

        consensus.reset();
        assert!(consensus.latest().is_none());
        assert_eq!(consensus.identity(), original);
        assert_eq!(consensus.rotate(1).unwrap(), first);
    }

    #[test]
    fn snapshot_restores_pending_rotation_across_handoff() {
        let mut consensus = TempoConsensus::new(B256::ZERO, NonZeroU64::new(2).unwrap());
        let first = consensus.rotate(0).unwrap();
        let snapshot = consensus.clone();
        mine(&mut consensus, 1);
        mine(&mut consensus, 2);
        assert_eq!(consensus.identity(), first);
        let second = consensus.rotate(2).unwrap();
        consensus = snapshot;
        assert!(consensus.latest().is_none());
        mine(&mut consensus, 1);
        mine(&mut consensus, 2);
        assert_eq!(consensus.identity(), first);
        assert_eq!(consensus.rotate(2).unwrap(), second);
    }

    #[test]
    fn header_context_obeys_hardfork_and_preparation_does_not_activate() {
        let mut consensus = TempoConsensus::new(B256::ZERO, NonZeroU64::new(2).unwrap());
        let original = consensus.identity();
        let mut header = TempoHeader::default();
        consensus.prepare_header(&mut header, TempoHardfork::T4).unwrap();
        assert!(header.consensus_context.is_none());
        assert!(header.inner.extra_data.is_empty());
        assert!(consensus.finalization(0).is_none());
        header.inner.number = 1;
        consensus.prepare_header(&mut header, TempoHardfork::T3).unwrap();
        assert!(header.consensus_context.is_none());
        let historical_hash = header.hash_slow();
        consensus.prepare_header(&mut header, TempoHardfork::T4).unwrap();
        assert!(header.consensus_context.is_some());
        assert_ne!(historical_hash, header.hash_slow());
        let rotated = consensus.rotate(0).unwrap();
        header.inner.number = 2;
        consensus.prepare_header(&mut header, TempoHardfork::T4).unwrap();
        assert_eq!(B256::from(header.consensus_context.unwrap().proposer), rotated.proposer);
        assert_eq!(consensus.identity(), original);
    }

    #[test]
    fn arithmetic_boundaries_fail_without_changing_state() {
        let mut consensus = TempoConsensus::new(B256::ZERO, NonZeroU64::MIN);
        let identity = consensus.identity();
        assert_eq!(consensus.rotate(u64::MAX), Err(TempoConsensusError::HeightOverflow));
        assert_eq!(consensus.rotate(u64::MAX - 1), Err(TempoConsensusError::EpochOverflow));
        let mut header = TempoHeader::default();
        header.inner.number = u64::MAX;
        let before = header.clone();
        assert_eq!(
            consensus.prepare_header(&mut header, TempoHardfork::T4),
            Err(TempoConsensusError::EpochOverflow)
        );
        assert_eq!(header, before);
        assert_eq!(consensus.identity(), identity);
        consensus.state.counter = u64::MAX;
        assert_eq!(consensus.rotate(0), Err(TempoConsensusError::CounterOverflow));
        assert_eq!(consensus.identity(), identity);

        let consensus = TempoConsensus::new(B256::ZERO, NonZeroU64::new(u64::MAX).unwrap());
        header.inner.number = u64::MAX - 1;
        consensus.prepare_header(&mut header, TempoHardfork::T4).unwrap();
        assert_eq!(header.consensus_context.unwrap().view, u64::MAX);
        let outcome = OnchainDkgOutcome::decode(header.inner.extra_data.as_ref()).unwrap();
        assert_eq!(outcome.epoch, 1);
    }

    fn mine(consensus: &mut TempoConsensus, height: u64) -> TempoHeader {
        let mut header = TempoHeader::default();
        header.inner.number = height;
        consensus.prepare_header(&mut header, TempoHardfork::T4).unwrap();
        let block = Block::new(header.clone().into(), Default::default());
        let finalization = consensus.finalize(&block, header.hash_slow(), TempoHardfork::T4);
        assert_eq!(finalization.digest, header.hash_slow());
        header
    }
}
