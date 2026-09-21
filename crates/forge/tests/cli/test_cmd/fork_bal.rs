//! Transaction-hash fork cache warming against a locally mined parent and transaction prefix.

use alloy_primitives::{Address, B256, U256, address, bytes};
use anvil::{EthereumHardfork, NodeConfig, NodeHandle, spawn};
use axum::{Json, Router, routing::post};
use foundry_test_utils::TestCommand;
use parking_lot::Mutex;
use serde_json::{Value, json};
use std::{
    sync::Arc,
    time::{Duration, Instant},
};
use tokio::task::JoinHandle;

const COUNTER: Address = address!("000000000000000000000000000000000000ba10");
const BAL_METHOD: &str = "eth_getBlockAccessListByBlockHash";

async fn rpc(endpoint: &str, method: &str, params: Value) -> Value {
    let response = reqwest::Client::new()
        .post(endpoint)
        .json(&json!({"jsonrpc": "2.0", "id": 1, "method": method, "params": params}))
        .send()
        .await
        .unwrap()
        .json::<Value>()
        .await
        .unwrap();
    assert!(response.get("error").is_none(), "{method}: {response}");
    response["result"].clone()
}

struct Fixture {
    handle: NodeHandle,
    parent: Value,
    transactions: [B256; 3],
    pending: B256,
}

impl Fixture {
    async fn new() -> Self {
        let (api, handle) = spawn(
            NodeConfig::test()
                .with_chain_id(Some(1u64))
                .with_hardfork(Some(EthereumHardfork::Cancun.into()))
                .with_genesis_timestamp(Some(1_800_000_000u64))
                .with_no_mining(true),
        )
        .await;
        // Every transaction reads slot one and increments slot zero.
        api.anvil_set_code(COUNTER, bytes!("6001545060005460010160005500")).await.unwrap();
        api.anvil_set_storage_at(COUNTER, U256::ZERO, B256::from(U256::from(6))).await.unwrap();
        api.anvil_set_storage_at(COUNTER, U256::from(1), B256::from(U256::from(19))).await.unwrap();
        let endpoint = handle.http_endpoint();
        let sender = handle.dev_wallets().next().unwrap().address();
        let send = |nonce| {
            json!([{"from": sender, "to": COUNTER, "nonce": format!("0x{nonce:x}"),
                    "gas": "0x30d40", "gasPrice": "0x77359400"}])
        };
        rpc(&endpoint, "eth_sendTransaction", send(0)).await;
        api.mine_one().await.unwrap();
        let parent = rpc(&endpoint, "eth_getBlockByNumber", json!(["latest", false])).await;
        assert_eq!(
            rpc(&endpoint, "eth_getStorageAt", json!([COUNTER, "0x0", "latest"])).await,
            json!(B256::from(U256::from(7))),
        );
        let mut transactions = [B256::ZERO; 3];
        for (index, hash) in transactions.iter_mut().enumerate() {
            *hash = serde_json::from_value(
                rpc(&endpoint, "eth_sendTransaction", send(index + 1)).await,
            )
            .unwrap();
        }
        api.mine_one().await.unwrap();
        let block = rpc(&endpoint, "eth_getBlockByNumber", json!(["latest", false])).await;
        assert_eq!(block["transactions"], json!(transactions));
        assert_eq!(block["parentHash"], parent["hash"]);
        let pending =
            serde_json::from_value(rpc(&endpoint, "eth_sendTransaction", send(4)).await).unwrap();
        Self { handle, parent, transactions, pending }
    }
}

#[derive(Clone, Copy, Debug)]
enum Response {
    Valid,
    Unsupported,
    Null,
    Malformed,
    Invalid,
    WrongCommitment,
    Timeout,
    PreCancun,
    UnknownChain,
    Anvil,
}

struct Proxy {
    endpoint: String,
    requests: Arc<Mutex<Vec<Value>>>,
    task: JoinHandle<()>,
}

impl Proxy {
    async fn new(fixture: &Fixture, mode: Response) -> Self {
        let upstream = fixture.handle.http_endpoint();
        let client = reqwest::Client::new();
        let requests = Arc::new(Mutex::new(Vec::new()));
        let recorded = Arc::clone(&requests);
        let parent_hash = fixture.parent["hash"].clone();
        let app = Router::new().route(
            "/",
            post(move |Json(request): Json<Value>| {
                let upstream = upstream.clone();
                let client = client.clone();
                let recorded = Arc::clone(&recorded);
                let parent_hash = parent_hash.clone();
                async move {
                    recorded.lock().push(request.clone());
                    let method = request["method"].as_str().unwrap();
                    if (!matches!(mode, Response::Anvil)
                        && matches!(method, "anvil_nodeInfo" | "anvil_metadata"))
                        || (method == BAL_METHOD && matches!(mode, Response::Unsupported))
                    {
                        return Json(json!({"jsonrpc": "2.0", "id": request["id"],
                            "error": {"code": -32601, "message": "method not found"}}));
                    }
                    if method == BAL_METHOD {
                        let mut bal = json!([{
                            "address": COUNTER,
                            "storageChanges": [{"key": "0x0", "changes": [
                                {"index": "0x1", "value": "0x7"}
                            ]}],
                            "storageReads": ["0x1"],
                            "balanceChanges": [], "nonceChanges": [], "codeChanges": []
                        }]);
                        match mode {
                            Response::Null => bal = Value::Null,
                            Response::Malformed => bal = json!([{"address": "invalid"}]),
                            Response::Invalid => {
                                bal[0]["storageChanges"][0]["changes"][0]["index"] = json!("0xff");
                            }
                            Response::Timeout => return futures::future::pending().await,
                            _ => {}
                        }
                        return Json(json!({"jsonrpc": "2.0", "id": request["id"], "result": bal}));
                    }
                    let mut response = client
                        .post(upstream)
                        .json(&request)
                        .send()
                        .await
                        .unwrap()
                        .json::<Value>()
                        .await
                        .unwrap();
                    if method == "eth_chainId" && matches!(mode, Response::UnknownChain) {
                        response["result"] = json!("0x7a69");
                    }
                    if matches!(method, "eth_getBlockByHash" | "eth_getBlockByNumber") {
                        if matches!(mode, Response::PreCancun) {
                            response["result"]["timestamp"] = json!("0x60000000");
                        }
                        if matches!(mode, Response::WrongCommitment)
                            && response["result"]["hash"] == parent_hash
                        {
                            response["result"]["blockAccessListHash"] = json!(B256::ZERO);
                        }
                    }
                    Json(response)
                }
            }),
        );
        let listener = tokio::net::TcpListener::bind("127.0.0.1:0").await.unwrap();
        let endpoint = format!("http://{}", listener.local_addr().unwrap());
        let task = tokio::spawn(async move { axum::serve(listener, app).await.unwrap() });
        Self { endpoint, requests, task }
    }

    fn count(&self, method: &str) -> usize {
        self.requests.lock().iter().filter(|request| request["method"] == method).count()
    }

    fn slot_reads(&self, slot: U256) -> usize {
        self.requests
            .lock()
            .iter()
            .filter(|request| {
                request["method"] == "eth_getStorageAt"
                    && request["params"][0] == json!(COUNTER)
                    && serde_json::from_value::<U256>(request["params"][1].clone()).unwrap() == slot
            })
            .count()
    }

    fn assert_parent_bal(&self, fixture: &Fixture) {
        let requests = self.requests.lock();
        let calls =
            requests.iter().filter(|request| request["method"] == BAL_METHOD).collect::<Vec<_>>();
        assert!(!calls.is_empty(), "parent BAL was never requested");
        for request in calls {
            assert_eq!(request["params"], json!([fixture.parent["hash"]]));
        }
    }

    fn clear(&self) {
        self.requests.lock().clear();
    }
}

impl Drop for Proxy {
    fn drop(&mut self) {
        self.task.abort();
    }
}

const TEST: &str = r#"
interface Vm {
    function envString(string calldata) external returns (string memory);
    function envUint(string calldata) external returns (uint256);
    function envBytes32(string calldata) external returns (bytes32);
    function createFork(string calldata, uint256) external returns (uint256);
    function createFork(string calldata, bytes32) external returns (uint256);
    function createSelectFork(string calldata, uint256) external returns (uint256);
    function createSelectFork(string calldata, bytes32) external returns (uint256);
    function selectFork(uint256) external;
    function activeFork() external view returns (uint256);
    function rollFork(bytes32) external;
    function rollFork(uint256, bytes32) external;
    function load(address, bytes32) external view returns (bytes32);
    function store(address, bytes32, bytes32) external;
    function makePersistent(address) external;
    function snapshotState() external returns (uint256);
    function revertToState(uint256) external returns (bool);
}

contract ForkBalTest {
    Vm constant vm = Vm(address(uint160(uint256(keccak256("hevm cheat code")))));
    address constant counter = address(0xba10);

    function value() internal view returns (uint256) {
        return uint256(vm.load(counter, bytes32(0)));
    }

    function testForkBal() public {
        string memory url = vm.envString("BAL_RPC_URL");
        bytes32 target = vm.envBytes32("BAL_TARGET");
        uint256 parent = vm.envUint("BAL_PARENT");
        uint256 mode = vm.envUint("BAL_MODE");
        if (mode == 0) {
            vm.selectFork(vm.createFork(url, target));
        } else if (mode == 1) {
            vm.createSelectFork(url, target);
        } else if (mode == 2) {
            vm.createSelectFork(url, parent);
            vm.rollFork(target);
        } else {
            uint256 active = vm.createSelectFork(url, parent);
            uint256 inactive = vm.createFork(url, parent);
            vm.rollFork(inactive, target);
            require(vm.activeFork() == active, "inactive roll selected the fork");
            require(value() == 7, "inactive roll changed active state");
            vm.selectFork(inactive);
        }
        require(value() == vm.envUint("BAL_EXPECTED"), "wrong prefix state");
        require(uint256(vm.load(counter, bytes32(uint256(1)))) == 19, "lost read-only slot");
    }

    function testForkBalLifecycle() public {
        string memory url = vm.envString("BAL_RPC_URL");
        bytes32 target = vm.envBytes32("BAL_TARGET");
        uint256 first = vm.createSelectFork(url, target);
        require(value() == 9, "prefix missing");
        uint256 snapshot = vm.snapshotState();
        (bool ok,) = counter.call("");
        require(ok && value() == 10, "local transaction missing");
        require(vm.revertToState(snapshot) && value() == 9, "snapshot lost");
        vm.store(counter, bytes32(0), bytes32(uint256(90)));
        address persistent = address(0xba11);
        vm.store(persistent, bytes32(0), bytes32(uint256(42)));
        vm.makePersistent(persistent);
        uint256 second = vm.createSelectFork(url, target);
        require(value() == 9, "new fork inherited local write");
        require(uint256(vm.load(persistent, bytes32(0))) == 42, "persistent state lost");
        vm.store(counter, bytes32(0), bytes32(uint256(80)));
        vm.selectFork(first);
        require(value() == 90, "first fork local write lost");
        vm.selectFork(second);
        require(value() == 80, "second fork local write lost");
    }

    function testForkBalOrdinary() public {
        vm.createSelectFork(vm.envString("BAL_RPC_URL"), vm.envUint("BAL_PARENT"));
        require(value() == 7, "wrong ordinary fork");
    }
}
"#;

fn command<'a>(
    cmd: &'a mut TestCommand,
    fixture: &Fixture,
    proxy: &Proxy,
    target: B256,
    expected: u64,
    mode: u64,
    test: &str,
) -> &'a mut TestCommand {
    let parent = u64::from_str_radix(
        fixture.parent["number"].as_str().unwrap().trim_start_matches("0x"),
        16,
    )
    .unwrap();
    cmd.forge_fuse();
    cmd.cmd().env_remove("FOUNDRY_NO_FORK_BAL");
    cmd.env("BAL_RPC_URL", &proxy.endpoint);
    cmd.env("BAL_TARGET", target.to_string());
    cmd.env("BAL_PARENT", parent.to_string());
    cmd.env("BAL_MODE", mode.to_string());
    cmd.env("BAL_EXPECTED", expected.to_string());
    cmd.env("FOUNDRY_NO_STORAGE_CACHING", "true");
    cmd.env("FOUNDRY_DISABLE_NIGHTLY_WARNING", "true");
    cmd.args(["test", "--match-test", test, "--evm-version", "cancun"])
}

fn assert_test(cmd: &mut TestCommand, name: &str) {
    cmd.assert_success().stdout_eq(format!(
        "...\nRan 1 test for test/ForkBal.t.sol:ForkBalTest\n[PASS] {name}() ([GAS])\nSuite result: ok. 1 passed; 0 failed; 0 skipped; [ELAPSED]\n\nRan 1 test suite [ELAPSED]: 1 tests passed, 0 failed, 0 skipped (1 total tests)\n",
    ));
}

forgetest_async!(fork_bal_parent_cache_preserves_every_transaction_position, |prj, cmd| {
    let fixture = Fixture::new().await;
    let proxy = Proxy::new(&fixture, Response::Valid).await;
    prj.add_test("ForkBal.t.sol", TEST);
    for mode in 0..4 {
        for (index, target) in fixture.transactions.iter().enumerate() {
            let mut block_reads = Vec::new();
            for disabled in [false, true] {
                proxy.clear();
                command(
                    &mut cmd,
                    &fixture,
                    &proxy,
                    *target,
                    7 + index as u64,
                    mode,
                    r"^testForkBal\(\)$",
                );
                if disabled {
                    cmd.arg("--no-fork-bal");
                }
                assert_test(&mut cmd, "testForkBal");
                block_reads.push(proxy.count("eth_getBlockByHash"));
                if disabled {
                    assert_eq!(proxy.count(BAL_METHOD), 0);
                    assert!(proxy.slot_reads(U256::ZERO) > 0);
                } else {
                    proxy.assert_parent_bal(&fixture);
                    assert_eq!(proxy.slot_reads(U256::ZERO), 0, "mode={mode}, index={index}");
                }
                assert!(proxy.slot_reads(U256::from(1)) > 0, "read-only slots need RPC fallback");
            }
            assert_eq!(block_reads[0], block_reads[1], "BAL fetched an extra block: mode={mode}");
        }
    }
});

forgetest_async!(fork_bal_keeps_local_writes_snapshots_and_persistent_accounts, |prj, cmd| {
    let fixture = Fixture::new().await;
    let proxy = Proxy::new(&fixture, Response::Valid).await;
    prj.add_test("ForkBal.t.sol", TEST);
    for disabled in [false, true] {
        proxy.clear();
        command(
            &mut cmd,
            &fixture,
            &proxy,
            fixture.transactions[2],
            9,
            1,
            r"^testForkBalLifecycle\(\)$",
        );
        if disabled {
            cmd.arg("--no-fork-bal");
        }
        assert_test(&mut cmd, "testForkBalLifecycle");
        if !disabled {
            proxy.assert_parent_bal(&fixture);
            assert_eq!(proxy.slot_reads(U256::ZERO), 0);
        }
    }
});

forgetest_async!(fork_bal_config_and_environment_control_runtime_requests, |prj, cmd| {
    let fixture = Fixture::new().await;
    let proxy = Proxy::new(&fixture, Response::Valid).await;
    prj.add_test("ForkBal.t.sol", TEST);
    for (configured, environment, flag, enabled) in [
        (true, None, false, false),
        (false, Some("true"), false, false),
        (true, Some("false"), false, true),
        (false, Some("false"), true, false),
    ] {
        prj.update_config(|config| config.no_fork_bal = configured);
        proxy.clear();
        command(&mut cmd, &fixture, &proxy, fixture.transactions[2], 9, 1, r"^testForkBal\(\)$");
        if let Some(environment) = environment {
            cmd.env("FOUNDRY_NO_FORK_BAL", environment);
        }
        if flag {
            cmd.arg("--no-fork-bal");
        }
        assert_test(&mut cmd, "testForkBal");
        if enabled {
            proxy.assert_parent_bal(&fixture);
            assert_eq!(proxy.slot_reads(U256::ZERO), 0);
        } else {
            assert_eq!(proxy.count(BAL_METHOD), 0);
            assert!(proxy.slot_reads(U256::ZERO) > 0);
        }
    }
});

forgetest_async!(fork_bal_unusable_responses_fall_back_to_replay, |prj, cmd| {
    let fixture = Fixture::new().await;
    prj.add_test("ForkBal.t.sol", TEST);
    for mode in [
        Response::Unsupported,
        Response::Null,
        Response::Malformed,
        Response::Invalid,
        Response::WrongCommitment,
        Response::Timeout,
    ] {
        let proxy = Proxy::new(&fixture, mode).await;
        command(&mut cmd, &fixture, &proxy, fixture.transactions[2], 9, 1, r"^testForkBal\(\)$");
        let started = Instant::now();
        assert_test(&mut cmd, "testForkBal");
        assert!(
            started.elapsed() < Duration::from_secs(20),
            "optional BAL request delayed the fork: {mode:?}"
        );
        proxy.assert_parent_bal(&fixture);
        assert!(proxy.slot_reads(U256::ZERO) > 0, "invalid BAL was used: {mode:?}");
        let block_reads = proxy.count("eth_getBlockByHash");
        proxy.clear();
        command(&mut cmd, &fixture, &proxy, fixture.transactions[2], 9, 1, r"^testForkBal\(\)$")
            .arg("--no-fork-bal");
        assert_test(&mut cmd, "testForkBal");
        assert_eq!(proxy.count("eth_getBlockByHash"), block_reads, "extra block read: {mode:?}");
    }
});

forgetest_async!(fork_bal_skips_ineligible_ordinary_and_pending_forks, |prj, cmd| {
    let fixture = Fixture::new().await;
    prj.add_test("ForkBal.t.sol", TEST);
    for mode in [Response::PreCancun, Response::UnknownChain, Response::Anvil] {
        let proxy = Proxy::new(&fixture, mode).await;
        command(&mut cmd, &fixture, &proxy, fixture.transactions[0], 7, 1, r"^testForkBal\(\)$");
        assert_test(&mut cmd, "testForkBal");
        assert_eq!(proxy.count(BAL_METHOD), 0, "ineligible source: {mode:?}");
    }
    let proxy = Proxy::new(&fixture, Response::Valid).await;
    command(
        &mut cmd,
        &fixture,
        &proxy,
        fixture.transactions[2],
        7,
        1,
        r"^testForkBalOrdinary\(\)$",
    );
    assert_test(&mut cmd, "testForkBalOrdinary");
    assert_eq!(proxy.count(BAL_METHOD), 0);
    proxy.clear();
    command(&mut cmd, &fixture, &proxy, fixture.pending, 10, 1, r"^testForkBal\(\)$");
    assert_test(&mut cmd, "testForkBal");
    assert_eq!(proxy.count(BAL_METHOD), 0);
});
