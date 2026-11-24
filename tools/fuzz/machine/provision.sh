#!/usr/bin/env bash
# The base of the fuzzing machine, on a fresh Ubuntu 24.04: a swap file (the first build needs
# more than the 4 GB of memory), the packages, Rust stable and nightly with cargo-fuzz, opam and
# uv, unattended security updates, and lingering, so the user services run without a login.
set -euxo pipefail
if [ ! -f /swapfile ]; then
    sudo fallocate -l 4G /swapfile && sudo chmod 600 /swapfile && sudo mkswap /swapfile && sudo swapon /swapfile
    echo '/swapfile none swap sw 0 0' | sudo tee -a /etc/fstab
fi
export DEBIAN_FRONTEND=noninteractive
sudo apt-get update -q
sudo apt-get install -y -q build-essential clang lld llvm pkg-config git curl unzip m4 bubblewrap \
    zlib1g-dev libssl-dev jq python3 unattended-upgrades rsync
sudo dpkg-reconfigure -f noninteractive unattended-upgrades
[ -x ~/.cargo/bin/rustup ] || curl -sSf https://sh.rustup.rs | sh -s -- -y --profile minimal
. ~/.cargo/env
rustup toolchain install nightly --profile minimal
cargo +nightly install cargo-fuzz --locked
if [ ! -x /usr/local/bin/opam ]; then
    curl -fsSL https://opam.ocaml.org/install.sh -o /tmp/opam.sh
    (cd /tmp && sh opam.sh --download-only < /dev/null)
    sudo install -m 755 /tmp/opam-*-"$(uname -m)"-linux /usr/local/bin/opam
fi
opam init -y --disable-sandboxing --bare
[ -x ~/.local/bin/uv ] || curl -LsSf https://astral.sh/uv/install.sh | sh
sudo loginctl enable-linger "$USER"
