#!/bin/bash
set -e

echo "%%%%%% Testing default features %%%%%%"
cargo test
echo "%%%%%% Finished testing default features %%%%%%"

echo "%%%%%% Testing fnv %%%%%%"
cargo test --no-default-features --features fnv-hash,uuid-extras
echo "%%%%%% Finished fnv %%%%%%"

echo "%%%%%% Testing sip %%%%%%"
cargo test --no-default-features --features sip-hash,uuid-extras
echo "%%%%%% Finished sip %%%%%%"

# echo "%%%%%% Testing minimal features %%%%%%"
# cargo test --no-default-features
# echo "%%%%%% Finished minimal features %%%%%%"

