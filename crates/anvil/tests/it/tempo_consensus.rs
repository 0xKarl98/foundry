//! Tempo consensus certificates exercised through the public HTTP RPC.

use alloy_consensus::{
    Sealable, Typed2718, proofs::calculate_transaction_root, transaction::TxHashRef,
};
use alloy_primitives::{B256, Bytes, hex, keccak256};
use anvil::{NodeConfig, spawn};
use commonware_codec::{DecodeExt, Encode, ReadExt, varint::UInt};
use commonware_cryptography::bls12381::primitives::{
    group::{G1, G2},
    ops,
    variant::MinSig,
};
use foundry_evm::hardfork::FoundryHardfork;
use serde::{Deserialize, Serialize, de::DeserializeOwned};
use serde_json::{Value, json};
use std::{num::NonZeroU64, path::PathBuf};
use tempo_dkg_onchain_artifacts::OnchainDkgOutcome;
use tempo_evm::consensus::validate_body_against_header;
use tempo_hardfork::TempoHardfork;
use tempo_primitives::Block;

#[derive(Debug, Clone, PartialEq, Eq, Deserialize, Serialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct Identity {
    identity: Bytes,
    proposer: B256,
    from_epoch: u64,
    epoch_length: u64,
    participants: u32,
    quorum: u32,
}

#[derive(Debug, Clone, PartialEq, Eq, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct Finalization {
    epoch: u64,
    view: u64,
    digest: B256,
    certificate: String,
    block: Block,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct Latest {
    finalized: Option<Finalization>,
    notarized: Option<Finalization>,
}

async fn request(endpoint: &str, method: &str, params: Value) -> Value {
    reqwest::Client::new()
        .post(endpoint)
        .json(&json!({ "jsonrpc": "2.0", "id": 1, "method": method, "params": params }))
        .send()
        .await
        .unwrap()
        .error_for_status()
        .unwrap()
        .json()
        .await
        .unwrap()
}

async fn rpc<T: DeserializeOwned>(endpoint: &str, method: &str, params: Value) -> T {
    let response = request(endpoint, method, params).await;
    assert!(response.get("error").is_none(), "{method}: {response}");
    serde_json::from_value(response["result"].clone()).unwrap()
}

async fn mine(endpoint: &str) {
    rpc::<Value>(endpoint, "evm_mine", json!([])).await;
}

async fn finalization(endpoint: &str, height: u64) -> Finalization {
    rpc(endpoint, "consensus_getFinalization", json!([{ "height": height }])).await
}

fn assert_signature(identity: &Identity, certified: &Finalization) {
    let bytes = hex::decode(&certified.certificate).unwrap();
    assert_eq!(certified.certificate, hex::encode(&bytes));
    let mut cursor = bytes.as_slice();
    assert_eq!(UInt::<u64>::read(&mut cursor).unwrap().0, certified.epoch);
    assert_eq!(UInt::<u64>::read(&mut cursor).unwrap().0, certified.view);
    let round_length = bytes.len() - cursor.len();
    assert_eq!(UInt::<u64>::read(&mut cursor).unwrap().0, certified.view - 1);
    assert_eq!(&cursor[..32], certified.digest.as_slice());
    cursor = &cursor[32..];
    let proposal_length = bytes.len() - cursor.len();
    let vote = G1::read(&mut cursor).unwrap();
    let seed = G1::read(&mut cursor).unwrap();
    assert!(cursor.is_empty(), "certificate must not contain additional framing");
    let public = G2::decode(identity.identity.as_ref()).unwrap();
    ops::verify_message::<MinSig>(&public, b"TEMPO_FINALIZE", &bytes[..proposal_length], &vote)
        .unwrap();
    ops::verify_message::<MinSig>(&public, b"TEMPO_SEED", &bytes[..round_length], &seed).unwrap();

    let mut altered = bytes[..proposal_length].to_vec();
    *altered.last_mut().unwrap() ^= 1;
    assert!(ops::verify_message::<MinSig>(&public, b"TEMPO_FINALIZE", &altered, &vote).is_err());
    assert_eq!(certified.digest, certified.block.header.hash_slow());
    assert_eq!(certified.digest, keccak256(alloy_rlp::encode(&certified.block.header)));
    validate_body_against_header(&certified.block.body, &certified.block.header).unwrap();
    if let Some(context) = &certified.block.header.consensus_context {
        assert_eq!(B256::from(context.proposer), identity.proposer);
    }
}

async fn assert_eth_projection(endpoint: &str, certified: &Finalization) {
    let block: Value = rpc(
        endpoint,
        "eth_getBlockByNumber",
        json!([format!("{:#x}", certified.block.header.inner.number), false]),
    )
    .await;
    assert_eq!(block["hash"], json!(certified.digest));
    assert_eq!(
        block["consensusContext"],
        serde_json::to_value(certified.block.header.consensus_context.as_ref().unwrap()).unwrap()
    );
    let by_hash: Value =
        rpc(endpoint, "eth_getBlockByHash", json!([certified.digest, false])).await;
    assert_eq!(by_hash, block);
}

async fn assert_missing(endpoint: &str, query: Value, data: &str) {
    assert_eq!(
        request(endpoint, "consensus_getFinalization", json!([query])).await,
        json!({
            "jsonrpc": "2.0", "id": 1,
            "error": {
                "code": 503,
                "message": "the consensus subservice was not available, but the request can be retried later",
                "data": data,
            }
        })
    );
}

#[tokio::test(flavor = "multi_thread")]
async fn tempo_consensus_http_certificate_matches_tempo_block() {
    let (_, handle) = spawn(NodeConfig::test_tempo().with_no_mining(true)).await;
    let endpoint = handle.http_endpoint();
    let identity: Identity = rpc(&endpoint, "anvil_tempoConsensusIdentity", json!([])).await;
    assert_eq!(identity.identity.len(), 96);
    assert_eq!((identity.participants, identity.quorum, identity.epoch_length), (1, 1, 21_600));
    let latest: Latest = rpc(&endpoint, "consensus_getLatest", json!([])).await;
    assert!(latest.finalized.is_none());
    assert!(latest.notarized.is_none());
    assert_missing(&endpoint, json!("latest"), "certifications").await;
    assert_missing(&endpoint, json!({ "height": 0 }), "certificate").await;
    let genesis: Value = rpc(&endpoint, "eth_getBlockByNumber", json!(["0x0", false])).await;
    assert!(genesis.get("consensusContext").is_none_or(Value::is_null));

    mine(&endpoint).await;
    let certified = finalization(&endpoint, 1).await;
    assert_eq!((certified.epoch, certified.view), (0, 2));
    assert_signature(&identity, &certified);
    assert_eth_projection(&endpoint, &certified).await;
    let latest: Latest = rpc(&endpoint, "consensus_getLatest", json!([])).await;
    assert_eq!(latest.finalized.as_ref(), Some(&certified));
    assert!(latest.notarized.is_none());
    assert_eq!(
        rpc::<Finalization>(&endpoint, "consensus_getFinalization", json!(["latest"])).await,
        certified
    );
    assert_missing(&endpoint, json!({ "height": 2 }), "certificate").await;
    let uppercase = request(&endpoint, "consensus_getFinalization", json!(["Latest"])).await;
    assert_eq!(uppercase["error"]["code"], -32602);

    // Export the actual HTTP response for the independent native Simplex verifier.
    if let Some(path) = std::env::var_os("ANVIL_TEMPO_CONSENSUS_ARTIFACT") {
        std::fs::write(
            path,
            serde_json::to_vec_pretty(&json!({ "identity": identity, "finalization": certified }))
                .unwrap(),
        )
        .unwrap();
    }
}

#[tokio::test(flavor = "multi_thread")]
async fn tempo_consensus_identity_is_reproducible() {
    let config = NodeConfig::test_tempo().with_no_mining(true);
    let (_, first) = spawn(config.clone()).await;
    let (_, second) = spawn(config.with_tempo_consensus_seed(None)).await;
    let first_identity: Identity =
        rpc(&first.http_endpoint(), "anvil_tempoConsensusIdentity", json!([])).await;
    assert_eq!(
        first_identity,
        rpc::<Identity>(&second.http_endpoint(), "anvil_tempoConsensusIdentity", json!([])).await
    );
    let rotated: Identity =
        rpc(&first.http_endpoint(), "anvil_tempoRotateConsensusIdentity", json!([])).await;
    assert_ne!(rotated.identity, first_identity.identity);
    assert_ne!(rotated.proposer, first_identity.proposer);
    assert_eq!(rotated.from_epoch, 1);
}

#[tokio::test(flavor = "multi_thread")]
async fn tempo_consensus_rotation_boundary_and_snapshot() {
    let (_, handle) = spawn(
        NodeConfig::test_tempo()
            .with_no_mining(true)
            .with_tempo_epoch_length(NonZeroU64::new(3).unwrap()),
    )
    .await;
    let endpoint = handle.http_endpoint();
    let initial: Identity = rpc(&endpoint, "anvil_tempoConsensusIdentity", json!([])).await;
    let before_rotation: Value = rpc(&endpoint, "evm_snapshot", json!([])).await;
    let first: Identity = rpc(&endpoint, "anvil_tempoRotateConsensusIdentity", json!([])).await;
    let rotated: Identity = rpc(&endpoint, "anvil_tempoRotateConsensusIdentity", json!([])).await;
    assert_ne!(first.identity, rotated.identity);
    assert_eq!(rotated.from_epoch, 1);
    assert_eq!(
        rpc::<Identity>(&endpoint, "anvil_tempoConsensusIdentity", json!([])).await,
        initial
    );
    mine(&endpoint).await;
    let before_boundary: Value = rpc(&endpoint, "evm_snapshot", json!([])).await;
    mine(&endpoint).await;
    let boundary = finalization(&endpoint, 2).await;
    assert_signature(&initial, &boundary);
    let outcome =
        OnchainDkgOutcome::decode(boundary.block.header.inner.extra_data.as_ref()).unwrap();
    assert_eq!(outcome.epoch, 1);
    assert_eq!(outcome.network_identity().encode().as_ref(), rotated.identity.as_ref());
    assert_eq!(outcome.next_players.len(), 1);
    assert!(!outcome.is_next_full_dkg);
    mine(&endpoint).await;
    let next_epoch = finalization(&endpoint, 3).await;
    assert_eq!((next_epoch.epoch, next_epoch.view), (1, 1));
    assert_signature(&rotated, &next_epoch);
    assert_eth_projection(&endpoint, &next_epoch).await;
    assert_eq!(
        rpc::<Identity>(&endpoint, "anvil_tempoConsensusIdentity", json!([])).await,
        rotated
    );

    assert!(rpc::<bool>(&endpoint, "evm_revert", json!([before_boundary])).await);
    assert_eq!(
        rpc::<Identity>(&endpoint, "anvil_tempoConsensusIdentity", json!([])).await,
        initial
    );
    assert_missing(&endpoint, json!({ "height": 2 }), "certificate").await;
    assert_missing(&endpoint, json!({ "height": 3 }), "certificate").await;
    mine(&endpoint).await;
    let replacement = finalization(&endpoint, 2).await;
    assert_eq!(replacement.block.header.inner.extra_data, boundary.block.header.inner.extra_data);
    assert_signature(&initial, &replacement);
    mine(&endpoint).await;
    assert_signature(&rotated, &finalization(&endpoint, 3).await);

    assert!(rpc::<bool>(&endpoint, "evm_revert", json!([before_rotation])).await);
    assert_eq!(
        rpc::<Identity>(&endpoint, "anvil_tempoConsensusIdentity", json!([])).await,
        initial
    );
    assert_eq!(
        rpc::<Identity>(&endpoint, "anvil_tempoRotateConsensusIdentity", json!([])).await,
        first,
        "revert must restore the deterministic derivation counter"
    );
}

#[tokio::test(flavor = "multi_thread")]
async fn tempo_consensus_rotation_after_published_boundary() {
    let (_, handle) = spawn(
        NodeConfig::test_tempo()
            .with_no_mining(true)
            .with_tempo_epoch_length(NonZeroU64::new(3).unwrap()),
    )
    .await;
    let endpoint = handle.http_endpoint();
    let initial: Identity = rpc(&endpoint, "anvil_tempoConsensusIdentity", json!([])).await;
    mine(&endpoint).await;
    mine(&endpoint).await;
    let published = finalization(&endpoint, 2).await;
    let rotated: Identity = rpc(&endpoint, "anvil_tempoRotateConsensusIdentity", json!([])).await;
    assert_eq!(rotated.from_epoch, 2);
    assert_eq!(finalization(&endpoint, 2).await, published);
    mine(&endpoint).await;
    assert_signature(&initial, &finalization(&endpoint, 3).await);
    mine(&endpoint).await;
    mine(&endpoint).await;
    let boundary = finalization(&endpoint, 5).await;
    let outcome =
        OnchainDkgOutcome::decode(boundary.block.header.inner.extra_data.as_ref()).unwrap();
    assert_eq!(outcome.epoch, 2);
    assert_eq!(outcome.network_identity().encode().as_ref(), rotated.identity.as_ref());
    mine(&endpoint).await;
    assert_signature(&rotated, &finalization(&endpoint, 6).await);
}

#[tokio::test(flavor = "multi_thread")]
async fn tempo_consensus_rollback_reorg_reset() {
    let (_, handle) = spawn(
        NodeConfig::test_tempo()
            .with_no_mining(true)
            .with_tempo_epoch_length(NonZeroU64::new(3).unwrap()),
    )
    .await;
    let endpoint = handle.http_endpoint();
    let initial: Identity = rpc(&endpoint, "anvil_tempoConsensusIdentity", json!([])).await;
    let rotated: Identity = rpc(&endpoint, "anvil_tempoRotateConsensusIdentity", json!([])).await;
    for _ in 0..4 {
        mine(&endpoint).await;
    }
    let first = finalization(&endpoint, 1).await;
    rpc::<Value>(&endpoint, "anvil_rollback", json!([3])).await;
    assert_eq!(finalization(&endpoint, 1).await, first);
    assert_missing(&endpoint, json!({ "height": 4 }), "certificate").await;
    assert_eq!(
        rpc::<Identity>(&endpoint, "anvil_tempoConsensusIdentity", json!([])).await,
        initial
    );
    mine(&endpoint).await;
    mine(&endpoint).await;
    assert_signature(&rotated, &finalization(&endpoint, 3).await);

    rpc::<Value>(&endpoint, "anvil_setNextBlockTimestamp", json!([2_000_000_000])).await;
    rpc::<Value>(&endpoint, "anvil_reorg", json!([2, []])).await;
    assert_eq!(finalization(&endpoint, 1).await, first);
    for (height, identity) in [(2, &initial), (3, &rotated)] {
        let replacement = finalization(&endpoint, height).await;
        assert_signature(identity, &replacement);
        assert_eth_projection(&endpoint, &replacement).await;
    }

    rpc::<Value>(&endpoint, "anvil_reset", json!([])).await;
    assert_missing(&endpoint, json!("latest"), "certifications").await;
    assert_missing(&endpoint, json!({ "height": 1 }), "certificate").await;
    assert_eq!(
        rpc::<Identity>(&endpoint, "anvil_tempoConsensusIdentity", json!([])).await,
        initial
    );
    assert_eq!(
        rpc::<Identity>(&endpoint, "anvil_tempoRotateConsensusIdentity", json!([])).await,
        rotated
    );
    mine(&endpoint).await;
    assert_signature(&initial, &finalization(&endpoint, 1).await);
}

#[tokio::test(flavor = "multi_thread")]
async fn tempo_consensus_fork_history_and_local_certificates() {
    let (_, source) = spawn(NodeConfig::test_tempo().with_no_mining(true)).await;
    let source_endpoint = source.http_endpoint();
    for _ in 0..3 {
        mine(&source_endpoint).await;
    }
    let historical = finalization(&source_endpoint, 2).await;
    let (_, fork) = spawn(
        NodeConfig::test_tempo()
            .with_no_mining(true)
            .with_eth_rpc_url(Some(source_endpoint))
            .with_fork_block_number(Some(2u64))
            .with_tempo_consensus_seed(Some(B256::repeat_byte(0x42))),
    )
    .await;
    let endpoint = fork.http_endpoint();
    assert_eq!(finalization(&endpoint, 2).await, historical);
    assert_eq!(
        rpc::<Finalization>(&endpoint, "consensus_getFinalization", json!(["latest"])).await,
        historical
    );
    let latest: Latest = rpc(&endpoint, "consensus_getLatest", json!([])).await;
    assert_eq!(latest.finalized.as_ref(), Some(&historical));
    assert_missing(&endpoint, json!({ "height": 3 }), "certificate").await;
    mine(&endpoint).await;
    let local = finalization(&endpoint, 3).await;
    let identity: Identity = rpc(&endpoint, "anvil_tempoConsensusIdentity", json!([])).await;
    assert_signature(&identity, &local);
    assert_eth_projection(&endpoint, &local).await;
    assert_eq!(finalization(&endpoint, 2).await, historical);
    assert_eq!(
        rpc::<Finalization>(&endpoint, "consensus_getFinalization", json!(["latest"])).await,
        local
    );
    rpc::<Value>(&endpoint, "anvil_rollback", json!([1])).await;
    assert_eq!(
        rpc::<Finalization>(&endpoint, "consensus_getFinalization", json!(["latest"])).await,
        historical
    );
}

#[tokio::test(flavor = "multi_thread")]
async fn tempo_consensus_unavailable_on_ethereum() {
    let (_, handle) = spawn(NodeConfig::test().with_no_mining(true)).await;
    let endpoint = handle.http_endpoint();
    for (method, params) in [
        ("consensus_getFinalization", json!(["latest"])),
        ("consensus_getLatest", json!([])),
        ("anvil_tempoConsensusIdentity", json!([])),
        ("anvil_tempoRotateConsensusIdentity", json!([])),
    ] {
        assert_eq!(
            request(&endpoint, method, params).await,
            json!({ "jsonrpc": "2.0", "id": 1, "error": { "code": -32603, "message": "Not implemented" } })
        );
    }
    mine(&endpoint).await;
    let block: Value = rpc(&endpoint, "eth_getBlockByNumber", json!(["latest", false])).await;
    assert!(block.get("consensusContext").is_none());
}

#[tokio::test(flavor = "multi_thread")]
async fn tempo_consensus_single_block_epoch() {
    let (_, handle) = spawn(
        NodeConfig::test_tempo()
            .with_no_mining(true)
            .with_tempo_epoch_length(NonZeroU64::new(1).unwrap()),
    )
    .await;
    let endpoint = handle.http_endpoint();
    let initial: Identity = rpc(&endpoint, "anvil_tempoConsensusIdentity", json!([])).await;
    let rotated: Identity = rpc(&endpoint, "anvil_tempoRotateConsensusIdentity", json!([])).await;
    assert_eq!(rotated.from_epoch, 2);
    mine(&endpoint).await;
    let first = finalization(&endpoint, 1).await;
    assert_eq!((first.epoch, first.view), (1, 1));
    assert_signature(&initial, &first);
    let announcement =
        OnchainDkgOutcome::decode(first.block.header.inner.extra_data.as_ref()).unwrap();
    assert_eq!(announcement.epoch, 2);
    assert_eq!(announcement.network_identity().encode().as_ref(), rotated.identity.as_ref());
    mine(&endpoint).await;
    let second = finalization(&endpoint, 2).await;
    assert_eq!((second.epoch, second.view), (2, 1));
    assert_signature(&rotated, &second);
}

#[tokio::test(flavor = "multi_thread")]
async fn tempo_consensus_historical_header_format() {
    let (_, handle) = spawn(
        NodeConfig::test_tempo()
            .with_no_mining(true)
            .with_hardfork(Some(FoundryHardfork::Tempo(TempoHardfork::T3))),
    )
    .await;
    let endpoint = handle.http_endpoint();
    mine(&endpoint).await;
    let identity: Identity = rpc(&endpoint, "anvil_tempoConsensusIdentity", json!([])).await;
    let certified = finalization(&endpoint, 1).await;
    assert!(certified.block.header.consensus_context.is_none());
    assert_signature(&identity, &certified);
    let block: Value = rpc(&endpoint, "eth_getBlockByNumber", json!(["latest", false])).await;
    assert_eq!(block["hash"], json!(certified.digest));
    assert!(block.get("consensusContext").is_none());
}

#[tokio::test(flavor = "multi_thread")]
async fn tempo_consensus_nonempty_native_block_body() {
    let (_, handle) = spawn(NodeConfig::test_tempo().with_no_mining(true)).await;
    let endpoint = handle.http_endpoint();
    let accounts = handle.dev_accounts().collect::<Vec<_>>();
    let ethereum_hash: B256 = rpc(
        &endpoint,
        "eth_sendTransaction",
        json!([{
            "from": accounts[0],
            "to": accounts[2],
            "type": "0x2",
            "gas": "0xf4240",
        }]),
    )
    .await;
    let tempo_hash: B256 = rpc(
        &endpoint,
        "eth_sendTransaction",
        json!([{
            "from": accounts[1],
            "type": "0x76",
            "gas": "0xf4240",
            "calls": [{ "to": accounts[2], "value": "0x0", "input": "0x1234" }],
        }]),
    )
    .await;
    mine(&endpoint).await;
    let identity: Identity = rpc(&endpoint, "anvil_tempoConsensusIdentity", json!([])).await;
    let certified = finalization(&endpoint, 1).await;
    assert_signature(&identity, &certified);
    assert_eth_projection(&endpoint, &certified).await;
    let transactions = &certified.block.body.transactions;
    assert_eq!(transactions.len(), 2);
    assert_eq!(
        calculate_transaction_root(transactions),
        certified.block.header.inner.transactions_root
    );
    let mut types = transactions.iter().map(Typed2718::ty).collect::<Vec<_>>();
    types.sort_unstable();
    assert_eq!(types, [2, 0x76]);
    let mut hashes = transactions.iter().map(|tx| *tx.tx_hash()).collect::<Vec<_>>();
    hashes.sort_unstable();
    let mut expected = [ethereum_hash, tempo_hash];
    expected.sort_unstable();
    assert_eq!(hashes, expected);

    if let Some(path) = std::env::var_os("ANVIL_TEMPO_CONSENSUS_ARTIFACT") {
        std::fs::write(
            PathBuf::from(path).with_extension("nonempty.json"),
            serde_json::to_vec_pretty(&json!({ "identity": identity, "finalization": certified }))
                .unwrap(),
        )
        .unwrap();
    }
}

#[tokio::test(flavor = "multi_thread")]
async fn tempo_consensus_pruned_body_is_unavailable() {
    let (_, handle) = spawn(
        NodeConfig::test_tempo().with_no_mining(true).with_transaction_block_keeper(Some(1usize)),
    )
    .await;
    let endpoint = handle.http_endpoint();
    let accounts = handle.dev_accounts().collect::<Vec<_>>();
    rpc::<B256>(
        &endpoint,
        "eth_sendTransaction",
        json!([{ "from": accounts[0], "to": accounts[1], "type": "0x2", "gas": "0xf4240" }]),
    )
    .await;
    mine(&endpoint).await;
    assert_eq!(finalization(&endpoint, 1).await.block.body.transactions.len(), 1);
    mine(&endpoint).await;
    assert_missing(&endpoint, json!({ "height": 1 }), "block").await;
    let identity: Identity = rpc(&endpoint, "anvil_tempoConsensusIdentity", json!([])).await;
    assert_signature(&identity, &finalization(&endpoint, 2).await);
}

#[tokio::test(flavor = "multi_thread")]
async fn tempo_consensus_latest_survives_immediate_body_pruning() {
    let (_, handle) = spawn(
        NodeConfig::test_tempo().with_no_mining(true).with_transaction_block_keeper(Some(0usize)),
    )
    .await;
    let endpoint = handle.http_endpoint();
    let accounts = handle.dev_accounts().collect::<Vec<_>>();
    rpc::<B256>(
        &endpoint,
        "eth_sendTransaction",
        json!([{ "from": accounts[0], "to": accounts[1], "type": "0x2", "gas": "0xf4240" }]),
    )
    .await;
    mine(&endpoint).await;
    assert_missing(&endpoint, json!({ "height": 1 }), "block").await;
    let identity: Identity = rpc(&endpoint, "anvil_tempoConsensusIdentity", json!([])).await;
    let latest: Finalization = rpc(&endpoint, "consensus_getFinalization", json!(["latest"])).await;
    assert_eq!(latest.block.body.transactions.len(), 1);
    assert_signature(&identity, &latest);
    let state: Latest = rpc(&endpoint, "consensus_getLatest", json!([])).await;
    assert_eq!(state.finalized, Some(latest.clone()));

    let snapshot: Value = rpc(&endpoint, "evm_snapshot", json!([])).await;
    mine(&endpoint).await;
    assert!(rpc::<bool>(&endpoint, "evm_revert", json!([snapshot])).await);
    let state: Latest = rpc(&endpoint, "consensus_getLatest", json!([])).await;
    assert_eq!(state.finalized, Some(latest));
    rpc::<Value>(&endpoint, "anvil_rollback", json!([1])).await;
    let state: Latest = rpc(&endpoint, "consensus_getLatest", json!([])).await;
    assert!(state.finalized.is_none());
}

#[tokio::test(flavor = "multi_thread")]
async fn tempo_consensus_loaded_history_discards_certificates() {
    let (_, handle) = spawn(
        NodeConfig::test_tempo()
            .with_no_mining(true)
            .with_tempo_epoch_length(NonZeroU64::new(3).unwrap()),
    )
    .await;
    let endpoint = handle.http_endpoint();
    let initial: Identity = rpc(&endpoint, "anvil_tempoConsensusIdentity", json!([])).await;
    mine(&endpoint).await;
    let saved: Bytes = rpc(&endpoint, "anvil_dumpState", json!([])).await;
    let rotated: Identity = rpc(&endpoint, "anvil_tempoRotateConsensusIdentity", json!([])).await;
    mine(&endpoint).await;
    mine(&endpoint).await;
    assert_signature(&rotated, &finalization(&endpoint, 3).await);
    assert!(rpc::<bool>(&endpoint, "anvil_loadState", json!([saved])).await);
    assert_missing(&endpoint, json!("latest"), "certifications").await;
    assert_missing(&endpoint, json!({ "height": 1 }), "certificate").await;
    assert_missing(&endpoint, json!({ "height": 3 }), "certificate").await;
    assert_eq!(
        rpc::<Identity>(&endpoint, "anvil_tempoConsensusIdentity", json!([])).await,
        initial
    );
    mine(&endpoint).await;
    assert_signature(&initial, &finalization(&endpoint, 2).await);

    let (_, other) = spawn(
        NodeConfig::test_tempo()
            .with_no_mining(true)
            .with_genesis_timestamp(Some(1u64))
            .with_tempo_consensus_seed(Some(B256::repeat_byte(0x42))),
    )
    .await;
    let other_endpoint = other.http_endpoint();
    mine(&other_endpoint).await;
    mine(&other_endpoint).await;
    let different: Bytes = rpc(&other_endpoint, "anvil_dumpState", json!([])).await;
    assert!(rpc::<bool>(&endpoint, "anvil_loadState", json!([different])).await);
    assert_missing(&endpoint, json!("latest"), "certifications").await;
    assert_missing(&endpoint, json!({ "height": 2 }), "certificate").await;
    mine(&endpoint).await;
    assert_signature(&initial, &finalization(&endpoint, 3).await);
}

#[tokio::test(flavor = "multi_thread")]
async fn tempo_consensus_fork_reset_clears_local_identity_history() {
    let config = NodeConfig::test_tempo()
        .with_no_mining(true)
        .with_tempo_epoch_length(NonZeroU64::new(2).unwrap());
    let (_, source) =
        spawn(config.clone().with_tempo_consensus_seed(Some(B256::repeat_byte(0x42)))).await;
    let source_endpoint = source.http_endpoint();
    mine(&source_endpoint).await;
    let historical = finalization(&source_endpoint, 1).await;

    let (_, handle) = spawn(config).await;
    let endpoint = handle.http_endpoint();
    let initial: Identity = rpc(&endpoint, "anvil_tempoConsensusIdentity", json!([])).await;
    let first: Identity = rpc(&endpoint, "anvil_tempoRotateConsensusIdentity", json!([])).await;
    let second: Identity = rpc(&endpoint, "anvil_tempoRotateConsensusIdentity", json!([])).await;
    mine(&endpoint).await;
    assert_ne!(finalization(&endpoint, 1).await.digest, historical.digest);
    mine(&endpoint).await;
    assert_signature(&second, &finalization(&endpoint, 2).await);
    let pending: Identity = rpc(&endpoint, "anvil_tempoRotateConsensusIdentity", json!([])).await;
    assert_eq!(pending.from_epoch, 2);

    rpc::<Value>(
        &endpoint,
        "anvil_reset",
        json!([{ "forking": { "jsonRpcUrl": source_endpoint, "blockNumber": 1 } }]),
    )
    .await;
    assert_eq!(
        rpc::<Identity>(&endpoint, "anvil_tempoConsensusIdentity", json!([])).await,
        initial
    );
    assert_eq!(finalization(&endpoint, 1).await, historical);
    assert_eq!(
        rpc::<Finalization>(&endpoint, "consensus_getFinalization", json!(["latest"])).await,
        historical
    );
    let latest: Latest = rpc(&endpoint, "consensus_getLatest", json!([])).await;
    assert_eq!(latest.finalized.as_ref(), Some(&historical));
    assert!(latest.notarized.is_none());
    assert_missing(&endpoint, json!({ "height": 2 }), "certificate").await;

    // Neither the previously active key nor its pending successor survives a fork reset.
    for height in 2..=4 {
        mine(&endpoint).await;
        assert_signature(&initial, &finalization(&endpoint, height).await);
    }
    assert_eq!(finalization(&endpoint, 1).await, historical);
    let scheduled: Identity = rpc(&endpoint, "anvil_tempoRotateConsensusIdentity", json!([])).await;
    assert_eq!(scheduled.identity, first.identity);
    assert_eq!(scheduled.proposer, first.proposer);
    assert_eq!(scheduled.from_epoch, 3);

    rpc::<Value>(&endpoint, "anvil_reset", json!([])).await;
    assert_eq!(
        rpc::<Identity>(&endpoint, "anvil_tempoConsensusIdentity", json!([])).await,
        initial
    );
    assert_missing(&endpoint, json!("latest"), "certifications").await;
    assert_missing(&endpoint, json!({ "height": 1 }), "certificate").await;
    assert_missing(&endpoint, json!({ "height": 4 }), "certificate").await;
    let latest: Latest = rpc(&endpoint, "consensus_getLatest", json!([])).await;
    assert!(latest.finalized.is_none());
    assert!(latest.notarized.is_none());

    // The fork's pending epoch-three key must not activate on the fresh local chain.
    for height in 1..=6 {
        mine(&endpoint).await;
        let certified = finalization(&endpoint, height).await;
        assert_signature(&initial, &certified);
        assert_eth_projection(&endpoint, &certified).await;
    }
    let scheduled: Identity = rpc(&endpoint, "anvil_tempoRotateConsensusIdentity", json!([])).await;
    assert_eq!(scheduled.identity, first.identity);
    assert_eq!(scheduled.proposer, first.proposer);
    assert_eq!(scheduled.from_epoch, 4);
}
