#!/bin/bash
set -e

echo "%%%%%% Testing default features %%%%%%"
cargo test
echo "%%%%%% Finished testing default features %%%%%%"

echo "%%%%%% Testing no-fnv %%%%%%"
cargo test --no-default-features --features uuid-extras
echo "%%%%%% Finished no-fnv %%%%%%"

echo "%%%%%% Testing minimal features %%%%%%"
cargo test --no-default-features
echo "%%%%%% Finished minimal features %%%%%%"

