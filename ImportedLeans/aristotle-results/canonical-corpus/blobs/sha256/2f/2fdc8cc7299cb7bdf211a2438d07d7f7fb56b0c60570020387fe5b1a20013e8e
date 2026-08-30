# Monster Project - Quick Start Guide

## 🚀 Get Started in 5 Minutes

### **Prerequisites**
- Nix (for reproducible builds)
- Git
- 10GB free disk space

### **1. Clone & Build**
```bash
cd /home/mdupont/experiments/monster/onlyskills-repo

# Build all tools
nix-shell -p cargo rustc --run "cargo build --release"
```

### **2. Setup Storage**
```bash
./setup_storage_overlay.sh
```

### **3. Run Your First Analysis**
```bash
# Search code
./target/release/lightning_git_search . "monster"

# Sort into prime tower
./target/release/prime_tower_sorter .

# Analyze complexity
./target/release/knuth_search_lattice .
```

---

## 🎯 Core Tools

### **1. Lightning Git Search** ⚡
Fast multi-tier search with auto-optimization.

```bash
./target/release/lightning_git_search . "pattern"
```

**Output**: Search results + storage tier info + auto-promotion

### **2. Prime Tower Sorter** 🗼
Sort code into 71 levels by complexity.

```bash
./target/release/prime_tower_sorter .
```

**Output**: `prime_tower/level_XX_prime_YY/` directories

### **3. Knuth Search Lattice** 📊
Analyze search tools by complexity.

```bash
./target/release/knuth_search_lattice .
```

**Output**: `KNUTH_SEARCH_LATTICE.tex` (literate programming doc)

### **4. Unified Monster System** 🌟
Complete integration: Rust Syn + Prolog NLP + Parquet + Memory + Qwen + ZK.

```bash
./target/release/unified_monster_system
```

**Output**: Unified analysis with all 6 components

### **5. Syn Ingestion** 🦀
Parse Rust code with syn, analyze AST.

```bash
./target/release/syn_ingestion .
```

**Output**: `rust_syn_analysis.json`

### **6. Inode → ZK Arrows** 🔗
Map filesystem inodes to ZK proofs.

```bash
./target/release/inode_zk_arrows file.txt
```

**Output**: ZK proof + Monster prime + parquet shard

---

## 📚 Documentation

See [DOCUMENTATION_INDEX.md](DOCUMENTATION_INDEX.md) for complete docs.

**Quick Links:**
- [Lightning Search Guide](LIGHTNING_SEARCH_GUIDE.md)
- [Unified System](UNIFIED_SYSTEM.md)
- [Search Tools Inventory](SEARCH_TOOLS_INVENTORY.md)
- [Lattice Attempts Ranking](LATTICE_ATTEMPTS_RANKING.md)
- [Syn Ingestion Ranking](SYN_INGESTION_RANKING.md)
- [File Overlays Ranking](FILE_OVERLAYS_RANKING.md)

---

## 🔗 Complete Pipeline

```
1. Ingest Code
   ./target/release/syn_ingestion .
   
2. Sort by Complexity
   ./target/release/prime_tower_sorter .
   
3. Analyze Lattice
   ./target/release/knuth_search_lattice .
   
4. Search & Optimize
   ./target/release/lightning_git_search . "pattern"
   
5. Generate ZK Proofs
   ./target/release/inode_zk_arrows file.txt
   
6. Unified Analysis
   ./target/release/unified_monster_system
```

---

## 🎓 Examples

### **Example 1: Find all Monster primes**
```bash
./target/release/lightning_git_search . "71"
```

### **Example 2: Analyze complexity**
```bash
./target/release/prime_tower_sorter .
cat prime_tower/tower_summary.json | jq .
```

### **Example 3: Search and promote**
```bash
# Search (auto-promotes top 3)
./target/release/lightning_git_search . "important"

# Check tier
ls -la shmem/gpu/
```

### **Example 4: Complete analysis**
```bash
# Run all tools
./target/release/syn_ingestion .
./target/release/prime_tower_sorter .
./target/release/knuth_search_lattice .
./target/release/unified_monster_system
```

---

## 🐛 Troubleshooting

### **Build fails**
```bash
# Clean and rebuild
cargo clean
nix-shell -p cargo rustc --run "cargo build --release"
```

### **Storage not found**
```bash
# Run setup
./setup_storage_overlay.sh

# Verify
ls -la shmem/ storage/
```

### **Git grep fails**
```bash
# Initialize git repo
git init
git add .
git commit -m "Initial commit"
```

---

## 📊 What You Get

After running all tools:

```
onlyskills-repo/
├── prime_tower/              # 71 levels of sorted code
│   ├── level_00_prime_02/
│   ├── level_01_prime_03/
│   └── tower_summary.json
├── unified_shards/           # Parquet shards
│   ├── shard_00.parquet
│   └── shard_01.parquet
├── shmem/                    # Fast storage
│   ├── gpu/                  # Speed 2
│   └── (tmpfs)               # Speed 3
├── storage/
│   ├── fast/                 # Speed 11
│   └── bulk/                 # Speed 13
├── rust_syn_analysis.json    # AST analysis
└── KNUTH_SEARCH_LATTICE.tex  # Literate doc
```

---

## 🎯 Next Steps

1. **Explore the tower**
   ```bash
   cd prime_tower
   find . -name "*.rs" | head -10
   ```

2. **Read the docs**
   ```bash
   cat DOCUMENTATION_INDEX.md
   ```

3. **Run Prolog NLP**
   ```bash
   swipl -s zero_ontology_nlp.pl
   ?- nlp_analyze([match(file,1,col,"Monster Walk")], A).
   ```

4. **Check proofs**
   ```bash
   swipl -s inode_zk_arrow_proofs.pl
   ?- prove_arrow_system.
   ```

---

## ✅ Verification

Check everything works:

```bash
# 1. Build
cargo build --release

# 2. Setup
./setup_storage_overlay.sh

# 3. Test search
./target/release/lightning_git_search . "test"

# 4. Test sorter
./target/release/prime_tower_sorter .

# 5. Verify output
ls -la prime_tower/
```

If all commands succeed: **✅ You're ready!**

---

## 🌟 The Monster Stack

```
┌─────────────────────────────────────┐
│   Applications & Queries            │
├─────────────────────────────────────┤
│   Lightning Search (⚡ 13ms)        │
├─────────────────────────────────────┤
│   Prime Tower (🗼 71 levels)        │
├─────────────────────────────────────┤
│   Knuth Lattice (📊 complexity)     │
├─────────────────────────────────────┤
│   Unified System (🌟 6 components)  │
├─────────────────────────────────────┤
│   Syn Ingestion (🦀 AST)            │
├─────────────────────────────────────┤
│   Inode → ZK (🔗 proofs)            │
├─────────────────────────────────────┤
│   Storage Overlay (💾 4 tiers)      │
├─────────────────────────────────────┤
│   Parquet Shards (📦 71 shards)     │
├─────────────────────────────────────┤
│   Prolog NLP (🧠 826 lines)         │
└─────────────────────────────────────┘
```

**Status**: ✅ **Production Ready**

---

## 📞 Help

- **Docs**: See [DOCUMENTATION_INDEX.md](DOCUMENTATION_INDEX.md)
- **Issues**: Check troubleshooting section above
- **Examples**: See examples/ directory

**Happy Monstering!** 🎉
