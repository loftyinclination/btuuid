#!/usr/bin/env bash

set -euxo pipefail

export RUSTFLAGS=-Dwarnings

cargo +nightly fmt -- --check

cargo clippy
cargo clippy --features uuid
cargo clippy --features defmt
cargo clippy --features serde
cargo clippy --all-features
