# Native Tempo certificate verification

This independent verifier reads an artifact containing the results of
`anvil_tempoConsensusIdentity` and `consensus_getFinalization`. It decodes the block
using `tempo_primitives::Block` and the certificate using Commonware's native
`Finalization<Scheme<PublicKey, MinSig>, Digest>`, then verifies the final header
hash, transaction/ommer/withdrawal commitments, and both signatures. A different
public key or a mutated digest, parent view, or epoch must fail verification.

The verifier is a separate Cargo workspace because `commonware-consensus` is not
in Foundry's lockfile. Its full consensus runtime must not become an Anvil
production dependency. Its generated lockfile and target directory are ignored;
the protocol crates and Tempo revision are pinned in its manifest.

The `tempo-consensus-compat` job in `.github/workflows/ci-tempo.yml` runs this
check on pull requests, including forks, without RPC credentials. It starts local
Anvil nodes and verifies artifacts for both an empty block and a block containing
ordinary EIP-1559 and Tempo AA transactions.

From the repository root, reproduce the same checks:

```sh
export ANVIL_TEMPO_CONSENSUS_ARTIFACT=/tmp/tempo-consensus.json
cargo test --locked -p anvil --test it --no-default-features --features cli,optimism \
  tempo_consensus::tempo_consensus_http_certificate_matches_tempo_block -- --exact
cargo test --locked -p anvil --test it --no-default-features --features cli,optimism \
  tempo_consensus::tempo_consensus_nonempty_native_block_body -- --exact
test -s "$ANVIL_TEMPO_CONSENSUS_ARTIFACT"
test -s "${ANVIL_TEMPO_CONSENSUS_ARTIFACT%.json}.nonempty.json"

export CARGO_TARGET_DIR="$PWD/crates/anvil/tests/fixtures/tempo-consensus-compat/target"
cargo run --manifest-path crates/anvil/tests/fixtures/tempo-consensus-compat/Cargo.toml
ANVIL_TEMPO_CONSENSUS_ARTIFACT="${ANVIL_TEMPO_CONSENSUS_ARTIFACT%.json}.nonempty.json" \
  cargo run --locked --manifest-path crates/anvil/tests/fixtures/tempo-consensus-compat/Cargo.toml
```

The first verifier run resolves its separate, ignored lockfile; the second reuses
it with `--locked`. Neither run changes Foundry's workspace dependency graph.
CI disables incremental compilation and debug information to limit disk use.

The verifier also accepts the artifact on standard input when the environment
variable is unset. The artifact has this shape:

```json
{
  "identity": { "identity": "0x<96-byte compressed G2 public key>" },
  "finalization": {
    "epoch": 0,
    "view": 2,
    "digest": "0x<32-byte final Tempo header hash>",
    "certificate": "<native finalization bytes, hex without 0x>",
    "block": { "header": {}, "body": {} }
  }
}
```

The block fields above are abbreviated; the real artifact contains the complete
Tempo block. Commonware's `sha256::Digest` is used only as its native fixed
32-byte payload container, with the same codec as Tempo's `Digest(B256)` wrapper;
the actual block hash remains Keccak-256 over the RLP-encoded `TempoHeader`.
