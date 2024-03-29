# `eth-tx-proof` powered by Plonky2's zkEVM

Similar to [`eth-proof`](https://github.com/wborgeaud/eth-proof) but for transaction proofs.

## Quick Start

There are two ways to run this prover. The simplest way to get started is
to use the `in-memory` runtime of
[Paladin](https://github.com/0xPolygonZero/paladin). This requires
very little setup, but it's not really suitable for a large scale
test. The other method for testing the prover is to leverage an
[AMQP](https://en.wikipedia.org/wiki/Advanced_Message_Queuing_Protocol)
like [RabbitMQ](https://en.wikipedia.org/wiki/RabbitMQ) to distribute
workload over many workers.

### Setup

Before running the prover, you'll need to compile the
application. This command should do the trick:

```bash
env RUSTFLAGS='-C target-cpu=native' cargo build --release
```

You should end up with two binaries in your `target/release`
folder. One is called `worker` and the other is `leader`. Typically,
we'll install these somewhere in our `$PATH` for convenience.

Once you have application available, you'll need to create a block
[witness](https://nmohnblatt.github.io/zk-jargon-decoder/definitions/witness.html)
which essentially serves as the input for the prover. Assuming you've
deployed the `leader` binary, you should be able to generate a witness
like this:

```bash
paladin-leader rpc -u $RPC_URL -t 0x2f0faea6778845b02f9faf84e7e911ef12c287ce7deb924c5925f3626c77906e > 0x2f0faea6778845b02f9faf84e7e911ef12c287ce7deb924c5925f3626c77906e.json
```

You'll need access to an Ethereum RPC in order to run this
command. The input argument is a transaction hash and in particular it
is the *last* transaction has in the block.

Once you've successfully generated a witness, you're ready to start
proving either with the `in-memory` runtime or the `amqp` runtime.

### In Memory Proving

Running the prover with the `in-memory` flag requires no setup. You
can attempt to generate a proof with a command like this.

```bash
env RUST_MIN_STACK=33554432 \
ARITHMETIC_CIRCUIT_SIZE="15..28" \
BYTE_PACKING_CIRCUIT_SIZE="9..28" \
CPU_CIRCUIT_SIZE="12..28" \
KECCAK_CIRCUIT_SIZE="14..28" \
KECCAK_SPONGE_CIRCUIT_SIZE="9..28" \
LOGIC_CIRCUIT_SIZE="12..28" \
MEMORY_CIRCUIT_SIZE="17..30" \
paladin-leader prove \
--runtime in-memory \
--num-workers 1 \
--input-witness 0x2f0faea6778845b02f9faf84e7e911ef12c287ce7deb924c5925f3626c77906e.json
```

The circuit parameters here are meant to be compatible with virtually
all Ethereum blocks. This will create a block proof from an input
state root of the preceding block. You can adjust the `--num-workers`
flag based on the number of available compute resources. As a rule of
thumb, you'd probably want at least 8 cores per worker. It's also
worth noting that you'll probably want at least 40GB of physical
memory to run the prover.

### AMQP Proving

Proving in a distributed compute environment depends on an AMQP
server. We're not going to cover the setup of RabbitMQ, but assuming
you have something like that available you can run a "leader" which
distribute proving tasks to a collection of "workers" which actually
do the proving work.

In order to run the workers, you'll use a command like:

```bash
env RUST_MIN_STACK=33554432 \
ARITHMETIC_CIRCUIT_SIZE="15..28" \
BYTE_PACKING_CIRCUIT_SIZE="9..28" \
CPU_CIRCUIT_SIZE="12..28" \
KECCAK_CIRCUIT_SIZE="14..28" \
KECCAK_SPONGE_CIRCUIT_SIZE="9..28" \
LOGIC_CIRCUIT_SIZE="12..28" \
MEMORY_CIRCUIT_SIZE="17..30" \
paladin-worker --runtime amqp --amqp-uri=amqp://localhost:5672
```

This will start the worker and have it await tasks. Depending on the
size of your machine, you may be able to run several workers on the
same operating system. An example [systemd
service](./deploy/paladin-worker@.service) is included. Once that
service is installed, you could enable and start 16 workers on the
same VM like this:

```bash
seq 0 15 | xargs -I xxx systemctl enable paladin-worker@xxx
seq 0 15 | xargs -I xxx systemctl start paladin-worker@xxx
```

Now that you have your pool of paladin workers, you can start proving
with a command like this:

```bash
paladin-leader prove \
--runtime amqp \
--amqp-uri=amqp://localhost:5672 \
--input-witness 0x2f0faea6778845b02f9faf84e7e911ef12c287ce7deb924c5925f3626c77906e.json
```

This command will run the same way as the `in-memory` mode except that
the leader itself isn't doing the work. The separate worker processes
are doing the heavy lifting.


## License

Licensed under either of:

* Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
* MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

The SPDX license identifier for this project is `MIT OR Apache-2.0`.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted for inclusion in the work by you,
as defined in the Apache-2.0 license, shall be dual licensed as above, without any additional terms or conditions.
