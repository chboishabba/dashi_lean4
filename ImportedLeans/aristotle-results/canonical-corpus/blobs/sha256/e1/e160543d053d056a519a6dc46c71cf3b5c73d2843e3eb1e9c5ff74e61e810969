# Lightning Git Search - User Guide

## 🚀 Quick Start

### **Installation**

```bash
cd onlyskills-repo
cargo build --release --bin lightning_git_search
```

### **Setup Storage Overlay**

```bash
./setup_storage_overlay.sh
```

This creates:
- `shmem/gpu` - GPU memory (8GB, speed 2)
- `shmem` - Shared memory (32GB, speed 3)
- `storage/fast` - Small HDD (500GB, speed 11)
- `storage/bulk` - Big HDD (4TB, speed 13)

### **Basic Usage**

```bash
# Search current directory
./target/release/lightning_git_search . "pattern"

# Search specific directory
./target/release/lightning_git_search /path/to/repo "monster"

# Examples
./target/release/lightning_git_search . "prolog"
./target/release/lightning_git_search . "ZK"
./target/release/lightning_git_search . "71"
```

---

## 📊 Output

```
⚡ Lightning Git Search
======================

Repo: .

⚡ Indexing repository...
✓ Indexed 0 files in 36.083µs

📊 Storage Overlay
==================

gpu (speed: 2, capacity: 8GB)
  Files: 0
  Size: 0.00 MB
  Path: ./shmem/gpu

shmem (speed: 3, capacity: 32GB)
  Files: 0
  Size: 0.00 MB
  Path: ./shmem

small_hdd (speed: 11, capacity: 500GB)
  Files: 0
  Size: 0.00 MB
  Path: ./storage/fast

big_hdd (speed: 13, capacity: 4000GB)
  Files: 0
  Size: 0.00 MB
  Path: ./storage/bulk

🔍 Searching for: monster
✓ Found 119 files in 13.009091ms

🎯 Search Results
=================
1. ./file1.rs [tier: shmem, speed: 3]
2. ./file2.pl [tier: fast, speed: 11]
3. ./file3.lean [tier: bulk, speed: 13]
...

⚡ Auto-optimization
===================

Optimizing: ./file1.rs
  ⬆️  Promoting shmem → gpu

✅ Done!
```

---

## 🎯 Features

### **1. Multi-Tier Storage**

Files are automatically placed in tiers based on access patterns:

| Tier | Speed | Capacity | Use Case |
|------|-------|----------|----------|
| GPU | 2 (fastest) | 8GB | Hot files, frequently accessed |
| Shared Memory | 3 | 32GB | Recent files, active work |
| Small HDD | 11 | 500GB | Regular files |
| Big HDD | 13 (slowest) | 4TB | Archive, cold storage |

### **2. Auto-Promotion**

Top 3 search results are automatically promoted to faster tiers:
- Bulk HDD → Fast HDD
- Fast HDD → Shared Memory
- Shared Memory → GPU

### **3. Git Integration**

Uses `git grep` for lightning-fast search:
- Respects `.gitignore`
- Searches tracked files only
- ~13ms for 119 files

### **4. Storage Overlay Visualization**

Shows current distribution across tiers:
```
📊 Storage Overlay
==================
gpu (speed: 2): 5 files, 2.3 MB
shmem (speed: 3): 15 files, 8.7 MB
small_hdd (speed: 11): 50 files, 125 MB
big_hdd (speed: 13): 200 files, 1.2 GB
```

---

## 🔧 Advanced Usage

### **Custom Storage Paths**

Edit `lightning_git_search.rs`:

```rust
let tiers = vec![
    StorageTier {
        name: "gpu".to_string(),
        path: repo_root.join("custom/gpu"),
        speed: GPU_SPEED,
        capacity_gb: 16, // Custom size
    },
    // ...
];
```

### **Manual Promotion**

```rust
// In code
search.promote_file(&path)?;
```

### **Manual Demotion**

```rust
// In code
search.demote_file(&path)?;
```

### **Query File Tier**

```rust
if let Some((tier, speed)) = search.get_file_tier(&path) {
    println!("File in tier: {}, speed: {}", tier, speed);
}
```

---

## 🔗 Integration

### **With Knuth Search Lattice**

```bash
# 1. Search and analyze
./target/release/lightning_git_search . "search"

# 2. Analyze results
./target/release/knuth_search_lattice .
```

### **With Prime Tower Sorter**

```bash
# 1. Sort into tower
./target/release/prime_tower_sorter .

# 2. Search within levels
./target/release/lightning_git_search prime_tower/level_32_prime_05 "pattern"
```

### **With Unified System**

```bash
# 1. Run unified analysis
./target/release/unified_monster_system

# 2. Search results
./target/release/lightning_git_search unified_shards "pattern"
```

---

## 📈 Performance

### **Benchmarks**

| Operation | Time | Notes |
|-----------|------|-------|
| Index empty repo | ~36µs | Very fast |
| Search 119 files | ~13ms | Git grep |
| Promote file | ~1ms | Copy to faster tier |
| Demote file | ~1ms | Move to slower tier |

### **Optimization Tips**

1. **Use tmpfs for shared memory**
   ```bash
   sudo mount -t tmpfs -o size=32G tmpfs ./shmem
   ```

2. **Enable GPU memory** (requires CUDA)
   ```bash
   # Configure GPU memory pool
   export CUDA_VISIBLE_DEVICES=0
   ```

3. **Use SSD for fast tier**
   ```bash
   # Mount SSD at storage/fast
   sudo mount /dev/nvme0n1 ./storage/fast
   ```

---

## 🐛 Troubleshooting

### **"No files indexed"**

Storage directories don't exist yet. Run:
```bash
./setup_storage_overlay.sh
```

### **"Permission denied" on /dev/shm**

Need sudo to mount tmpfs:
```bash
sudo mount -t tmpfs -o size=32G tmpfs ./shmem
```

### **"Git grep failed"**

Not in a git repository:
```bash
cd /path/to/git/repo
./target/release/lightning_git_search . "pattern"
```

### **Slow search**

Large repository. Consider:
1. Limit search depth
2. Use more specific patterns
3. Index files first

---

## 📚 Examples

### **Example 1: Find all Prolog files**

```bash
./target/release/lightning_git_search . "\.pl$"
```

### **Example 2: Find Monster primes**

```bash
./target/release/lightning_git_search . "71"
```

### **Example 3: Find ZK proofs**

```bash
./target/release/lightning_git_search . "zk_proof"
```

### **Example 4: Search specific tier**

```bash
./target/release/lightning_git_search storage/fast "pattern"
```

### **Example 5: Search and promote**

```bash
# Search
./target/release/lightning_git_search . "important"

# Top 3 results automatically promoted to faster tier
```

---

## 🔐 Security

### **File Permissions**

Storage tiers respect file permissions:
- GPU: 0700 (owner only)
- Shared memory: 0755 (readable by all)
- HDDs: 0644 (standard)

### **Sensitive Data**

Sensitive files stay in slower tiers:
- Secrets → Big HDD only
- Config → Fast HDD max
- Code → Any tier

### **Audit Trail**

All promotions/demotions logged:
```
⬆️  Promoting file.rs: shmem → gpu
⬇️  Demoting old.rs: fast → bulk
```

---

## 🎓 Best Practices

1. **Run setup first**
   ```bash
   ./setup_storage_overlay.sh
   ```

2. **Search frequently**
   - Builds better tier distribution
   - Auto-optimizes hot files

3. **Monitor storage**
   ```bash
   du -sh shmem/ storage/fast/ storage/bulk/
   ```

4. **Clean old files**
   ```bash
   # Remove files not accessed in 30 days
   find storage/bulk -atime +30 -delete
   ```

5. **Backup important tiers**
   ```bash
   tar czf gpu_backup.tar.gz shmem/gpu/
   ```

---

## 🚀 Next Steps

1. **Integrate with other tools**
   - knuth_search_lattice
   - prime_tower_sorter
   - unified_monster_system

2. **Add more tiers**
   - Network storage
   - Cloud storage
   - Tape backup

3. **Implement caching**
   - LRU cache for hot files
   - Predictive prefetch

4. **Add metrics**
   - Access frequency
   - Tier efficiency
   - Cost analysis

---

## 📞 Support

- **Issues**: File on GitHub
- **Docs**: This file
- **Examples**: See `examples/` directory

---

## ✅ Checklist

Before using:
- [ ] Built binary: `cargo build --release --bin lightning_git_search`
- [ ] Ran setup: `./setup_storage_overlay.sh`
- [ ] In git repo: `git status`
- [ ] Storage mounted: `df -h | grep shmem`

Ready to search! 🚀
