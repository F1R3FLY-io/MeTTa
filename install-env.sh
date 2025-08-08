#!/bin/bash

# MeTTa Development Environment Installation Script
# Universal installer for WSL and Linux systems
# Based on WSL.txt with hardcoded versions

set -e  # Exit on any error

echo "=== MeTTa Development Environment Installation ==="
echo "Universal installer for WSL and Linux systems"
echo "Installing with hardcoded versions from WSL.txt"
echo ""

# Hardcoded versions from WSL.txt
JAVA_VERSION="21.0.7-tem"
SCALA_VERSION="3.4.1"
SBT_VERSION="1.11.3"
BNFC_VERSION="2.9.5"
ALEX_VERSION="3.5.3.0"
HAPPY_VERSION="2.1.5"
GHC_VERSION="9.6.7"
CABAL_VERSION="3.12.1.0"

# Function to check if command exists
command_exists() {
    command -v "$1" >/dev/null 2>&1
}

# Function to print status
print_status() {
    echo "[INFO] $1"
}

print_error() {
    echo "[ERROR] $1" >&2
}

# Detect if running in WSL
if grep -qi microsoft /proc/version 2>/dev/null; then
    print_status "Detected WSL environment"
    IS_WSL=true
else
    print_status "Detected native Linux environment"
    IS_WSL=false
fi

# Update system packages
print_status "Updating system packages..."
sudo apt update
sudo apt upgrade -y

# Install basic development tools
print_status "Installing basic development tools..."
sudo apt install -y unzip zip gcc g++ build-essential curl libffi-dev libffi8 libgmp-dev libgmp10 libncurses-dev pkg-config dos2unix

# Install SDKMAN if not already installed
if ! command_exists sdk; then
    print_status "Installing SDKMAN..."
    curl -s "https://get.sdkman.io" | bash
    source "$HOME/.sdkman/bin/sdkman-init.sh"
else
    print_status "SDKMAN already installed, sourcing..."
    source "$HOME/.sdkman/bin/sdkman-init.sh"
fi

# Install Java with hardcoded version
print_status "Installing Java $JAVA_VERSION..."
sdk install java $JAVA_VERSION || true
sdk use java $JAVA_VERSION

# Install Scala with hardcoded version
print_status "Installing Scala $SCALA_VERSION..."
sdk install scala $SCALA_VERSION || true
sdk use scala $SCALA_VERSION

# Install SBT with hardcoded version
print_status "Installing SBT $SBT_VERSION..."
sdk install sbt $SBT_VERSION || true
sdk use sbt $SBT_VERSION

# Install GHCup and Haskell tools
if ! command_exists ghcup; then
    print_status "Installing GHCup and Haskell tools..."
    curl --proto '=https' --tlsv1.2 -sSf https://get-ghcup.haskell.org | BOOTSTRAP_HASKELL_NONINTERACTIVE=1 sh
    source "$HOME/.ghcup/env"
else
    print_status "GHCup already installed, sourcing..."
    source "$HOME/.ghcup/env"
fi

# Install specific GHC version
print_status "Installing GHC $GHC_VERSION..."
ghcup install ghc $GHC_VERSION
ghcup set ghc $GHC_VERSION

# Install specific Cabal version
print_status "Installing Cabal $CABAL_VERSION..."
ghcup install cabal $CABAL_VERSION
ghcup set cabal $CABAL_VERSION

# Install Stack (recommended version)
print_status "Installing Stack (recommended)..."
ghcup install stack recommended
ghcup set stack recommended

# Update cabal package list
print_status "Updating Cabal package list..."
cabal update

# Install BNFC
print_status "Installing BNFC $BNFC_VERSION..."
cabal install BNFC

# Install Alex
print_status "Installing Alex $ALEX_VERSION..."
cabal install alex

# Install Happy
print_status "Installing Happy $HAPPY_VERSION..."
cabal install happy

# Verify installations with expected versions
print_status "Verifying installations..."
echo "Java version (expected: $JAVA_VERSION):"
java --version
echo ""
echo "Scala version (expected: $SCALA_VERSION):"
scala --version
echo ""
echo "SBT version (expected: $SBT_VERSION):"
sbt --version
echo ""
echo "GHC version (expected: $GHC_VERSION):"
ghc --version
echo ""
echo "Cabal version (expected: $CABAL_VERSION):"
cabal --version
echo ""
echo "BNFC version (expected: $BNFC_VERSION):"
bnfc --version
echo ""
echo "Alex version (expected: $ALEX_VERSION):"
alex --version
echo ""
echo "Happy version (expected: $HAPPY_VERSION):"
happy --version
echo ""

# Setup MeTTa project if we're in the right directory
if [ -f "./build" ] && [ -f "./clean" ]; then
    print_status "Setting up MeTTa project..."
    dos2unix ./build
    dos2unix ./clean
    chmod +x ./build
    chmod +x ./clean
    
    print_status "Cleaning and building MeTTa project..."
    ./clean
    ./build
    
    print_status "MeTTa project built successfully!"
else
    print_status "MeTTa build scripts not found in current directory."
    print_status "Please navigate to the MeTTa project directory and run:"
    print_status "  dos2unix ./build && dos2unix ./clean"
    print_status "  chmod +x ./build && chmod +x ./clean"
    print_status "  ./clean && ./build"
fi

# Add GHCup to shell configuration
print_status "Adding GHCup to shell configuration..."
SHELL_NAME=$(basename "$SHELL")
case "$SHELL_NAME" in
    "bash")
        SHELL_CONFIG="$HOME/.bashrc"
        ;;
    "zsh")
        SHELL_CONFIG="$HOME/.zshrc"
        ;;
    "fish")
        SHELL_CONFIG="$HOME/.config/fish/config.fish"
        ;;
    *)
        SHELL_CONFIG="$HOME/.profile"
        ;;
esac

# Add GHCup source line if not already present
if [ -f "$SHELL_CONFIG" ] && ! grep -q "source.*ghcup/env" "$SHELL_CONFIG"; then
    echo "" >> "$SHELL_CONFIG"
    echo "# Added by MeTTa installer" >> "$SHELL_CONFIG"
    echo "source ~/.ghcup/env" >> "$SHELL_CONFIG"
    print_status "Added GHCup source to $SHELL_CONFIG"
elif [ ! -f "$SHELL_CONFIG" ]; then
    echo "# Added by MeTTa installer" > "$SHELL_CONFIG"
    echo "source ~/.ghcup/env" >> "$SHELL_CONFIG"
    print_status "Created $SHELL_CONFIG and added GHCup source"
else
    print_status "GHCup source already present in $SHELL_CONFIG"
fi

print_status "Installation completed successfully!"
if [ "$IS_WSL" = true ]; then
    print_status "WSL-specific setup completed."
else
    print_status "Linux-specific setup completed."
fi
print_status "GHCup has been added to your shell configuration ($SHELL_CONFIG)."
print_status "You may need to restart your terminal or run: source $SHELL_CONFIG"
print_status "For SDKMAN: source ~/.sdkman/bin/sdkman-init.sh"