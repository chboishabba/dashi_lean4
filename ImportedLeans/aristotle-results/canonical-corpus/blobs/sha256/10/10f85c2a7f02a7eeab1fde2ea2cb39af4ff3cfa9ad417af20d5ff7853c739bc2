// Lightning-fast Git repo search with GPU/shared memory + tiered HDD storage
use std::collections::HashMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::Instant;

// Monster prime speeds for storage tiers
const GPU_SPEED: u32 = 2;        // Fastest (like L1)
const SHMEM_SPEED: u32 = 3;      // Shared memory (like L2)
const SMALL_HDD_SPEED: u32 = 11; // Small HDD (like SSD)
const BIG_HDD_SPEED: u32 = 13;   // Big HDD (slower)

#[derive(Debug, Clone)]
struct StorageTier {
    name: String,
    path: PathBuf,
    speed: u32,
    capacity_gb: u64,
}

#[derive(Debug)]
struct FileMetadata {
    path: PathBuf,
    size_bytes: u64,
    access_count: u64,
    last_access: std::time::SystemTime,
    tier: String,
}

struct LightningSearch {
    tiers: Vec<StorageTier>,
    file_index: HashMap<PathBuf, FileMetadata>,
    repo_root: PathBuf,
}

impl LightningSearch {
    fn new(repo_root: PathBuf) -> Self {
        let tiers = vec![
            StorageTier {
                name: "gpu".to_string(),
                path: repo_root.join("shmem/gpu"),
                speed: GPU_SPEED,
                capacity_gb: 8, // 8GB GPU memory
            },
            StorageTier {
                name: "shmem".to_string(),
                path: repo_root.join("shmem"),
                speed: SHMEM_SPEED,
                capacity_gb: 32, // 32GB shared memory
            },
            StorageTier {
                name: "small_hdd".to_string(),
                path: repo_root.join("storage/fast"),
                speed: SMALL_HDD_SPEED,
                capacity_gb: 500, // 500GB small HDD
            },
            StorageTier {
                name: "big_hdd".to_string(),
                path: repo_root.join("storage/bulk"),
                speed: BIG_HDD_SPEED,
                capacity_gb: 4000, // 4TB big HDD
            },
        ];

        Self {
            tiers,
            file_index: HashMap::new(),
            repo_root,
        }
    }

    // Index all files in repo
    fn index_repo(&mut self) -> std::io::Result<()> {
        println!("⚡ Indexing repository...");
        let start = Instant::now();

        let tiers_clone: Vec<_> = self.tiers.iter()
            .map(|t| (t.path.clone(), t.name.clone()))
            .collect();

        for (path, name) in tiers_clone {
            if path.exists() {
                self.index_directory(&path, &name)?;
            }
        }

        println!("✓ Indexed {} files in {:?}", self.file_index.len(), start.elapsed());
        Ok(())
    }

    fn index_directory(&mut self, dir: &Path, tier: &str) -> std::io::Result<()> {
        if !dir.exists() {
            return Ok(());
        }

        for entry in fs::read_dir(dir)? {
            let entry = entry?;
            let path = entry.path();

            if path.is_dir() {
                self.index_directory(&path, tier)?;
            } else if path.is_file() {
                let metadata = fs::metadata(&path)?;
                self.file_index.insert(
                    path.clone(),
                    FileMetadata {
                        path: path.clone(),
                        size_bytes: metadata.len(),
                        access_count: 0,
                        last_access: metadata.accessed().unwrap_or(std::time::SystemTime::now()),
                        tier: tier.to_string(),
                    },
                );
            }
        }
        Ok(())
    }

    // Search using git grep (fastest)
    fn git_search(&self, pattern: &str) -> Vec<PathBuf> {
        let start = Instant::now();
        println!("🔍 Searching for: {}", pattern);

        let output = Command::new("git")
            .args(&["grep", "-l", pattern])
            .current_dir(&self.repo_root)
            .output()
            .expect("git grep failed");

        let results: Vec<PathBuf> = String::from_utf8_lossy(&output.stdout)
            .lines()
            .map(|line| self.repo_root.join(line))
            .collect();

        println!("✓ Found {} files in {:?}", results.len(), start.elapsed());
        results
    }

    // Get file tier and speed
    fn get_file_tier(&self, path: &Path) -> Option<(String, u32)> {
        self.file_index.get(path).map(|meta| {
            let tier = self.tiers.iter().find(|t| t.name == meta.tier)?;
            Some((tier.name.clone(), tier.speed))
        })?
    }

    // Promote hot files to faster tier
    fn promote_file(&mut self, path: &Path) -> std::io::Result<()> {
        let meta = self.file_index.get(path).ok_or_else(|| {
            std::io::Error::new(std::io::ErrorKind::NotFound, "File not in index")
        })?;

        let current_tier = self.tiers.iter().position(|t| t.name == meta.tier).unwrap();
        
        if current_tier == 0 {
            println!("  Already in fastest tier (GPU)");
            return Ok(());
        }

        let target_tier = &self.tiers[current_tier - 1];
        let target_path = target_tier.path.join(path.file_name().unwrap());

        println!("  ⬆️  Promoting {} → {}", meta.tier, target_tier.name);
        
        fs::create_dir_all(target_tier.path.parent().unwrap())?;
        fs::copy(path, &target_path)?;
        
        // Update index
        if let Some(meta) = self.file_index.get_mut(path) {
            meta.tier = target_tier.name.clone();
            meta.path = target_path;
        }

        Ok(())
    }

    // Demote cold files to slower tier
    fn demote_file(&mut self, path: &Path) -> std::io::Result<()> {
        let meta = self.file_index.get(path).ok_or_else(|| {
            std::io::Error::new(std::io::ErrorKind::NotFound, "File not in index")
        })?;

        let current_tier = self.tiers.iter().position(|t| t.name == meta.tier).unwrap();
        
        if current_tier == self.tiers.len() - 1 {
            println!("  Already in slowest tier (big HDD)");
            return Ok(());
        }

        let target_tier = &self.tiers[current_tier + 1];
        let target_path = target_tier.path.join(path.file_name().unwrap());

        println!("  ⬇️  Demoting {} → {}", meta.tier, target_tier.name);
        
        fs::create_dir_all(target_tier.path.parent().unwrap())?;
        fs::copy(path, &target_path)?;
        
        if let Some(meta) = self.file_index.get_mut(path) {
            meta.tier = target_tier.name.clone();
            meta.path = target_path;
        }

        Ok(())
    }

    // Show storage overlay
    fn show_overlay(&self) {
        println!("\n📊 Storage Overlay");
        println!("==================");
        
        for tier in &self.tiers {
            let files: Vec<_> = self.file_index.values()
                .filter(|m| m.tier == tier.name)
                .collect();
            
            let total_size: u64 = files.iter().map(|f| f.size_bytes).sum();
            let total_mb = total_size as f64 / 1_048_576.0;
            
            println!("\n{} (speed: {}, capacity: {}GB)", tier.name, tier.speed, tier.capacity_gb);
            println!("  Files: {}", files.len());
            println!("  Size: {:.2} MB", total_mb);
            println!("  Path: {}", tier.path.display());
        }
    }
}

fn main() {
    let repo_root = std::env::args()
        .nth(1)
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from("."));

    println!("⚡ Lightning Git Search");
    println!("======================\n");
    println!("Repo: {}\n", repo_root.display());

    let mut search = LightningSearch::new(repo_root.clone());

    // Index repository
    if let Err(e) = search.index_repo() {
        eprintln!("Error indexing: {}", e);
        return;
    }

    // Show storage overlay
    search.show_overlay();

    // Example search
    let pattern = std::env::args().nth(2).unwrap_or_else(|| "monster".to_string());
    let results = search.git_search(&pattern);

    println!("\n🎯 Search Results");
    println!("=================");
    
    for (i, path) in results.iter().take(10).enumerate() {
        if let Some((tier, speed)) = search.get_file_tier(path) {
            println!("{}. {} [tier: {}, speed: {}]", i + 1, path.display(), tier, speed);
        } else {
            println!("{}. {} [not indexed]", i + 1, path.display());
        }
    }

    if results.len() > 10 {
        println!("... and {} more", results.len() - 10);
    }

    // Promote frequently accessed files
    println!("\n⚡ Auto-optimization");
    println!("===================");
    
    for path in results.iter().take(3) {
        if search.file_index.contains_key(path) {
            println!("\nOptimizing: {}", path.display());
            if let Err(e) = search.promote_file(path) {
                eprintln!("  Error: {}", e);
            }
        }
    }

    println!("\n✅ Done!");
}
