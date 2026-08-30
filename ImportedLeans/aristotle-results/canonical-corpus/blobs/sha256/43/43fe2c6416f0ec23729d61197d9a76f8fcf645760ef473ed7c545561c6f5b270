#!/bin/bash
# Clone Multramate's mathematical repositories

REPOS_DIR="multramate-repos"
mkdir -p "$REPOS_DIR"
cd "$REPOS_DIR"

echo "Cloning Multramate's repositories..."

# Core mathematical repos
git clone https://github.com/Multramate/IC-GANT.git
git clone https://github.com/Multramate/Cam-GANT.git
git clone https://github.com/Multramate/ArithmeticStatistics.git
git clone https://github.com/Multramate/EllipticCurves.git
git clone https://github.com/Multramate/FldFunFin.git

# Haskell implementations
git clone https://github.com/Multramate/elliptic-curve.git
git clone https://github.com/Multramate/galois-field.git
git clone https://github.com/Multramate/pairing.git

echo "Done! Repositories cloned to $REPOS_DIR/"

# Add Multramate as remote to existing MonsterLean
echo ""
echo "Adding Multramate's mathlib4 as remote to MonsterLean..."
cd ../MonsterLean
git remote add multramate https://github.com/Multramate/mathlib4.git
git fetch multramate
echo "Multramate remote added to MonsterLean!"
