# OxiZ installation script for Windows
# OxiZ is a pure Rust SMT solver that can replace Z3

$oxiz_version = "0.1.3"

Write-Host "Installing oxiz version $oxiz_version..." -ForegroundColor Green

# Check if cargo is installed
try {
    $null = Get-Command cargo -ErrorAction Stop
} catch {
    Write-Host "Error: cargo is not installed. Please install Rust from https://rustup.rs/" -ForegroundColor Red
    exit 1
}

# Install oxiz-cli from crates.io
Write-Host "Installing oxiz-cli from crates.io..." -ForegroundColor Yellow
cargo install oxiz-cli --version $oxiz_version

# Check if installation was successful
try {
    $oxizPath = (Get-Command oxiz -ErrorAction Stop).Path
    Write-Host "✓ oxiz installed successfully" -ForegroundColor Green
    Write-Host "oxiz location: $oxizPath" -ForegroundColor Cyan
    & oxiz --version
    
    Write-Host ""
    Write-Host "To use oxiz with Verus, set the VERUS_OXIZ_PATH environment variable:" -ForegroundColor Yellow
    Write-Host "  `$env:VERUS_OXIZ_PATH = '$oxizPath'" -ForegroundColor Cyan
    Write-Host ""
    Write-Host "Or add to your PowerShell profile for persistence:" -ForegroundColor Yellow
    Write-Host "  Add-Content `$PROFILE ""`$env:VERUS_OXIZ_PATH = '$oxizPath'""" -ForegroundColor Cyan
    Write-Host ""
    Write-Host "Or pass --solver=oxiz to verus when running verification." -ForegroundColor Yellow
} catch {
    Write-Host "Error: oxiz installation failed" -ForegroundColor Red
    exit 1
}
