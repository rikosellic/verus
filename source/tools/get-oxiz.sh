#! /bin/bash -eu

# OxiZ installation script for Unix-like systems
# OxiZ is a pure Rust SMT solver that can replace Z3

oxiz_version="0.1.3"

echo "Installing oxiz version $oxiz_version..."

# Check if cargo is installed
if ! command -v cargo &> /dev/null; then
    echo "Error: cargo is not installed. Please install Rust from https://rustup.rs/"
    exit 1
fi

# Install oxiz-cli from crates.io
echo "Installing oxiz-cli from crates.io..."
cargo install oxiz-cli --version "$oxiz_version"

# Check if installation was successful
if command -v oxiz &> /dev/null; then
    echo "✓ oxiz installed successfully"
    echo "oxiz location: $(which oxiz)"
    oxiz --version
else
    echo "Error: oxiz installation failed"
    exit 1
fi

echo ""
echo "To use oxiz with Verus, set the VERUS_OXIZ_PATH environment variable:"
echo "  export VERUS_OXIZ_PATH=$(which oxiz)"
echo ""
echo "Or pass --solver=oxiz to verus when running verification."
