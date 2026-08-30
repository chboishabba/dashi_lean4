#!/usr/bin/env bash
# ZK Circuit Compilation and Proof Generation

set -e

echo "🔐 WITNESS OF THE GLORY - ZK Proof Generation"
echo "=============================================="

# Check circom
if ! command -v circom &> /dev/null; then
    echo "❌ circom not found. Install: https://docs.circom.io/getting-started/installation/"
    exit 1
fi

# Check snarkjs
if ! command -v snarkjs &> /dev/null; then
    echo "❌ snarkjs not found. Install: npm install -g snarkjs"
    exit 1
fi

echo ""
echo "📦 [1/6] Compiling circuit..."
circom witness_of_glory.circom --r1cs --wasm --sym -o build/
echo "✓ Circuit compiled"

echo ""
echo "🔑 [2/6] Generating proving key..."
if [ ! -f "pot12_final.ptau" ]; then
    echo "  Downloading powers of tau..."
    wget https://hermez.s3-eu-west-1.amazonaws.com/powersOfTau28_hez_final_12.ptau -O pot12_final.ptau
fi
snarkjs groth16 setup build/witness_of_glory.r1cs pot12_final.ptau build/circuit_final.zkey
echo "✓ Proving key generated"

echo ""
echo "🔐 [3/6] Exporting verification key..."
snarkjs zkey export verificationkey build/circuit_final.zkey build/verification_key.json
echo "✓ Verification key exported"

echo ""
echo "📝 [4/6] Generating witness..."
node build/witness_of_glory_js/generate_witness.js build/witness_of_glory_js/witness_of_glory.wasm witness_input.json build/witness.wtns
echo "✓ Witness generated"

echo ""
echo "🎯 [5/6] Generating proof..."
snarkjs groth16 prove build/circuit_final.zkey build/witness.wtns build/proof.json build/public.json
echo "✓ Proof generated"

echo ""
echo "✅ [6/6] Verifying proof..."
snarkjs groth16 verify build/verification_key.json build/public.json build/proof.json
echo "✓ Proof verified"

echo ""
echo "=============================================="
echo "🎉 WITNESS OF THE GLORY PROVEN!"
echo ""
echo "Files generated:"
echo "  - build/witness_of_glory.r1cs (circuit)"
echo "  - build/circuit_final.zkey (proving key)"
echo "  - build/verification_key.json (verification key)"
echo "  - build/proof.json (ZK proof)"
echo "  - build/public.json (public inputs)"
echo ""
echo "Public inputs:"
echo "  - Total complexity: 2783"
echo "  - Node count: 9"
echo ""
echo "Proven without revealing:"
echo "  - Individual complexities"
echo "  - Shard assignments"
echo "  - Memory tiers"
echo ""
echo "✅ GLORY ACHIEVED"
