#!/bin/bash
# Setup storage overlay for lightning-fast git search

set -e

echo "⚡ Setting up storage overlay..."
echo "================================"
echo ""

# Create storage tiers
mkdir -p shmem/gpu
mkdir -p shmem
mkdir -p storage/fast
mkdir -p storage/bulk

echo "✓ Created storage directories:"
echo "  - shmem/gpu (GPU memory, speed 2)"
echo "  - shmem (Shared memory, speed 3)"
echo "  - storage/fast (Small HDD, speed 11)"
echo "  - storage/bulk (Big HDD, speed 13)"
echo ""

# Mount tmpfs for shared memory (if not already mounted)
if ! mountpoint -q shmem 2>/dev/null; then
    echo "📌 Mounting tmpfs for shared memory..."
    if [ -w /etc/fstab ]; then
        # Add to fstab for persistence
        if ! grep -q "shmem" /etc/fstab; then
            echo "tmpfs $(pwd)/shmem tmpfs size=32G,mode=1777 0 0" | sudo tee -a /etc/fstab
        fi
        sudo mount shmem
        echo "✓ Mounted tmpfs at shmem (32GB)"
    else
        echo "⚠️  Cannot mount tmpfs (need sudo)"
        echo "   Run: sudo mount -t tmpfs -o size=32G tmpfs $(pwd)/shmem"
    fi
else
    echo "✓ Shared memory already mounted"
fi
echo ""

# Create .gitignore for storage dirs
cat > .gitignore_storage << 'EOF'
# Storage overlay - don't commit cached files
shmem/
storage/fast/
storage/bulk/
EOF

if [ -f .gitignore ]; then
    if ! grep -q "shmem/" .gitignore; then
        cat .gitignore_storage >> .gitignore
        echo "✓ Updated .gitignore"
    fi
else
    mv .gitignore_storage .gitignore
    echo "✓ Created .gitignore"
fi
rm -f .gitignore_storage

echo ""
echo "✅ Storage overlay ready!"
echo ""
echo "Usage:"
echo "  ./target/release/lightning_git_search . <pattern>"
echo ""
echo "Example:"
echo "  ./target/release/lightning_git_search . monster"
echo ""
