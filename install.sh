#!/bin/bash

cd rapx
cargo fmt -q
cd ..

set -e

cargo install --path rapx

cargo rapx -help
