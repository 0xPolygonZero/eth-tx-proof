#/usr/bin/env bash
set -euxo pipefail

RPC_URL=${1:-$RPC_URL} # you'll need debug RPC enabled
if [[ -z "${transaction_hash:-}" ]]; then
    : fetching latest transaction hash from remote
    rpc_response=$(
        curl \
            "$RPC_URL" \
            --header "Content-type: application/json" \
            --request POST \
            --data '{ "jsonrpc":"2.0", "method": "eth_getBlockByNumber", "params": ["latest", false ], "id": 1 }' \
    )
    transaction_hash=$(
        jq --raw-output '.result.transactions | last' <<<"$rpc_response"
    )
fi

test_data="test-data"
mkdir -p -- "$test_data"
cargo run --bin leader -- rpc \
    --transaction-hash="$transaction_hash" \
    > "$test_data/$transaction_hash.json"