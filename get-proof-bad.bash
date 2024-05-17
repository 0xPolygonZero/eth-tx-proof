#/usr/bin/env bash
set -euxo pipefail

curl \
    "$RPC_URL" \
    --header "Content-type: application/json" \
    --request POST \
    --data \
'{ 
    "jsonrpc": "2.0",
    "method": "eth_getProof",
    "params": [
        "0x0000000000000068f116a894984e2db1123eb395",
        [
            "0x703229de9cdfff44d4bf2a2a05651a9d04de0ddae04a870c1f9fca9129922f0a",
            "0x98f3b0ea87a851ff72982e97289d29dbd1cde96fb36bf0e93b1e85656f4c1fac",
            "0xc8a8b941c57c04b2ed13df9037a0f24c6ba7d3ee0a00f6122014c0497c03e786",
            "0xe9261c7fa12cc2e441d35913903437a9625a86d745a633fe4fa013c164f413e1"
        ],
        "0x12f72b2"
    ],
    "id": 1
}' \
| jq '.result'