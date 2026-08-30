// Sort all Rust syn code into Monster Prime Tower (71 levels)
// Uses unified system to analyze and distribute code by complexity

use std::collections::HashMap;
use std::fs;
use std::path::PathBuf;
use walkdir::WalkDir;
use serde::{Serialize, Deserialize};

const MONSTER_PRIMES: [u8; 15] = [2,3,5,7,11,13,17,19,23,29,31,41,47,59,71];

#[derive(Debug, Clone, Serialize, Deserialize)]
struct TowerLevel {
    level: u8,
    prime: u8,
    files: Vec<FileEntry>,
    total_complexity: u64,
    avg_complexity: u64,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct FileEntry {
    path: PathBuf,
    functions: usize,
    structs: usize,
    enums: usize,
    complexity: u64,
}

struct PrimeTower {
    levels: HashMap<u8, TowerLevel>,
}

impl PrimeTower {
    fn new() -> Self {
        let mut levels = HashMap::new();
        for level in 0..71 {
            let prime = MONSTER_PRIMES.get(level as usize % 15).copied().unwrap_or(71);
            levels.insert(level, TowerLevel {
                level,
                prime,
                files: Vec::new(),
                total_complexity: 0,
                avg_complexity: 0,
            });
        }
        Self { levels }
    }

    fn analyze_rust_file(&self, path: &PathBuf) -> Option<FileEntry> {
        let content = fs::read_to_string(path).ok()?;
        let syntax = syn::parse_file(&content).ok()?;
        
        let mut functions = 0;
        let mut structs = 0;
        let mut enums = 0;
        
        for item in &syntax.items {
            match item {
                syn::Item::Fn(_) => functions += 1,
                syn::Item::Struct(_) => structs += 1,
                syn::Item::Enum(_) => enums += 1,
                _ => {}
            }
        }
        
        let lines = content.lines().count();
        let complexity = lines as u64 + 10 * functions as u64 + 5 * structs as u64 + 3 * enums as u64;
        
        Some(FileEntry {
            path: path.clone(),
            functions,
            structs,
            enums,
            complexity,
        })
    }

    fn add_file(&mut self, entry: FileEntry) {
        let level = (entry.complexity % 71) as u8;
        
        if let Some(tower_level) = self.levels.get_mut(&level) {
            tower_level.total_complexity += entry.complexity;
            tower_level.files.push(entry);
            tower_level.avg_complexity = tower_level.total_complexity / tower_level.files.len() as u64;
        }
    }

    fn visualize(&self) {
        println!("\n🗼 MONSTER PRIME TOWER (71 Levels)");
        println!("==================================\n");
        
        for level in (0..71).rev() {
            if let Some(tower_level) = self.levels.get(&level) {
                if !tower_level.files.is_empty() {
                    let bar_len = (tower_level.files.len() as f64 / 10.0).ceil() as usize;
                    let bar = "█".repeat(bar_len.min(50));
                    
                    println!("Level {:2} (prime {:2}): {:3} files {} avg: {}",
                        level,
                        tower_level.prime,
                        tower_level.files.len(),
                        bar,
                        tower_level.avg_complexity
                    );
                }
            }
        }
    }

    fn save_to_disk(&self) -> std::io::Result<()> {
        println!("\n💾 Saving tower to disk...");
        
        fs::create_dir_all("prime_tower")?;
        
        for (level, tower_level) in &self.levels {
            if tower_level.files.is_empty() {
                continue;
            }
            
            let level_dir = format!("prime_tower/level_{:02}_prime_{:02}", level, tower_level.prime);
            fs::create_dir_all(&level_dir)?;
            
            // Save metadata
            let metadata = serde_json::to_string_pretty(tower_level)?;
            fs::write(format!("{}/metadata.json", level_dir), metadata)?;
            
            // Copy files to level
            for (i, file) in tower_level.files.iter().enumerate() {
                if let Some(filename) = file.path.file_name() {
                    let dest = format!("{}/{:04}_{}", level_dir, i, filename.to_string_lossy());
                    fs::copy(&file.path, dest).ok();
                }
            }
            
            println!("  ✓ Level {:2}: {} files", level, tower_level.files.len());
        }
        
        // Save tower summary
        let summary = serde_json::to_string_pretty(&self.levels)?;
        fs::write("prime_tower/tower_summary.json", summary)?;
        
        println!("✅ Tower saved to ./prime_tower/");
        Ok(())
    }

    fn generate_report(&self) {
        println!("\n📊 TOWER STATISTICS");
        println!("===================\n");
        
        let total_files: usize = self.levels.values().map(|l| l.files.len()).sum();
        let total_complexity: u64 = self.levels.values().map(|l| l.total_complexity).sum();
        let occupied_levels = self.levels.values().filter(|l| !l.files.is_empty()).count();
        
        println!("Total files:       {}", total_files);
        println!("Total complexity:  {}", total_complexity);
        println!("Occupied levels:   {}/71", occupied_levels);
        println!("Avg complexity:    {}", total_complexity / total_files.max(1) as u64);
        
        println!("\nTop 5 levels by file count:");
        let mut levels: Vec<_> = self.levels.values().collect();
        levels.sort_by(|a, b| b.files.len().cmp(&a.files.len()));
        
        for (i, level) in levels.iter().take(5).enumerate() {
            if !level.files.is_empty() {
                println!("  {}. Level {} (prime {}): {} files, avg complexity {}",
                    i + 1, level.level, level.prime, level.files.len(), level.avg_complexity);
            }
        }
        
        println!("\nMost complex files:");
        let mut all_files: Vec<_> = self.levels.values()
            .flat_map(|l| &l.files)
            .collect();
        all_files.sort_by(|a, b| b.complexity.cmp(&a.complexity));
        
        for (i, file) in all_files.iter().take(5).enumerate() {
            println!("  {}. {} (complexity: {}, level: {})",
                i + 1,
                file.path.display(),
                file.complexity,
                (file.complexity % 71)
            );
        }
    }
}

fn main() {
    println!("🗼 SORTING RUST CODE INTO PRIME TOWER");
    println!("======================================\n");
    
    let base_path = std::env::args()
        .nth(1)
        .unwrap_or_else(|| ".".to_string());
    
    println!("Scanning: {}\n", base_path);
    
    let mut tower = PrimeTower::new();
    let mut processed = 0;
    let mut skipped = 0;
    
    for entry in WalkDir::new(&base_path)
        .max_depth(10)
        .into_iter()
        .filter_map(|e| e.ok())
        .filter(|e| e.path().extension().and_then(|s| s.to_str()) == Some("rs"))
    {
        if processed % 100 == 0 && processed > 0 {
            print!("\r  Processed: {} files...", processed);
        }
        
        if let Some(file_entry) = tower.analyze_rust_file(&entry.path().to_path_buf()) {
            tower.add_file(file_entry);
            processed += 1;
        } else {
            skipped += 1;
        }
    }
    
    println!("\r  Processed: {} files", processed);
    println!("  Skipped:   {} files\n", skipped);
    
    tower.visualize();
    tower.generate_report();
    tower.save_to_disk().ok();
    
    println!("\n✅ TOWER COMPLETE");
    println!("\nNext steps:");
    println!("  1. Explore: ls -la prime_tower/");
    println!("  2. View level: cat prime_tower/level_XX_prime_YY/metadata.json");
    println!("  3. Analyze: jq . prime_tower/tower_summary.json");
}
