// Knuth-style Analysis: Search Tools → ZK71 Lattice by Complexity
// "Let us change our traditional attitude to the construction of programs:
//  Instead of imagining that our main task is to instruct a computer what to do,
//  let us concentrate rather on explaining to human beings what we want a computer to do."
//  — Donald Knuth, Literate Programming (1984)

use std::collections::HashMap;
use std::fs;
use std::path::{Path, PathBuf};
use walkdir::WalkDir;

#[derive(Debug, Clone)]
struct SearchTool {
    path: PathBuf,
    name: String,
    lines: usize,
    functions: usize,
    structs: usize,
    complexity: u64,
    shard: u8,
    common_patterns: Vec<String>,
}

#[derive(Debug)]
struct ComplexityLattice {
    shards: [Vec<SearchTool>; 71],
    total_tools: usize,
}

impl ComplexityLattice {
    fn new() -> Self {
        Self {
            shards: std::array::from_fn(|_| Vec::new()),
            total_tools: 0,
        }
    }

    fn add_tool(&mut self, tool: SearchTool) {
        let shard = tool.shard as usize;
        self.shards[shard].push(tool);
        self.total_tools += 1;
    }

    fn analyze(&self) {
        println!("\n╔═══════════════════════════════════════════════════════════════╗");
        println!("║  KNUTH'S SEARCH LATTICE: ZK71 Shards by Complexity          ║");
        println!("╚═══════════════════════════════════════════════════════════════╝\n");

        println!("§1. Introduction\n");
        println!("We analyze {} search tools, sharding by complexity modulo 71.", self.total_tools);
        println!("Each shard represents a complexity class in the Monster lattice.\n");

        println!("§2. Distribution Across Shards\n");
        for (shard_num, tools) in self.shards.iter().enumerate() {
            if !tools.is_empty() {
                let total_complexity: u64 = tools.iter().map(|t| t.complexity).sum();
                let avg_complexity = total_complexity / tools.len() as u64;
                println!("  Shard {:2} ({:2} tools, avg complexity: {})", 
                    shard_num, tools.len(), avg_complexity);
                for tool in tools {
                    println!("    • {} (complexity: {})", tool.name, tool.complexity);
                }
            }
        }

        println!("\n§3. Common Patterns Analysis\n");
        self.find_common_patterns();

        println!("\n§4. Complexity Metrics\n");
        self.complexity_metrics();
    }

    fn find_common_patterns(&self) {
        let mut pattern_counts: HashMap<String, usize> = HashMap::new();

        for shard in &self.shards {
            for tool in shard {
                for pattern in &tool.common_patterns {
                    *pattern_counts.entry(pattern.clone()).or_insert(0) += 1;
                }
            }
        }

        let mut patterns: Vec<_> = pattern_counts.into_iter().collect();
        patterns.sort_by(|a, b| b.1.cmp(&a.1));

        println!("  Most common patterns across all tools:");
        for (pattern, count) in patterns.iter().take(10) {
            println!("    {:2}× {}", count, pattern);
        }
    }

    fn complexity_metrics(&self) {
        let all_tools: Vec<_> = self.shards.iter().flatten().collect();
        
        let total_lines: usize = all_tools.iter().map(|t| t.lines).sum();
        let total_functions: usize = all_tools.iter().map(|t| t.functions).sum();
        let total_structs: usize = all_tools.iter().map(|t| t.structs).sum();
        let total_complexity: u64 = all_tools.iter().map(|t| t.complexity).sum();

        println!("  Total lines:      {}", total_lines);
        println!("  Total functions:  {}", total_functions);
        println!("  Total structs:    {}", total_structs);
        println!("  Total complexity: {}", total_complexity);
        println!("  Avg complexity:   {}", total_complexity / all_tools.len() as u64);
    }
}

fn analyze_rust_file(path: &Path) -> Option<SearchTool> {
    let content = fs::read_to_string(path).ok()?;
    
    let lines = content.lines().count();
    let functions = content.matches("fn ").count();
    let structs = content.matches("struct ").count();
    
    // Complexity = lines + 10*functions + 5*structs
    let complexity = lines as u64 + 10 * functions as u64 + 5 * structs as u64;
    let shard = (complexity % 71) as u8;

    // Find common patterns
    let mut patterns = Vec::new();
    if content.contains("memmap") { patterns.push("memmap".to_string()); }
    if content.contains("/dev/shm") { patterns.push("shared_memory".to_string()); }
    if content.contains("Monster") { patterns.push("monster_prime".to_string()); }
    if content.contains("shard") { patterns.push("sharding".to_string()); }
    if content.contains("index") { patterns.push("indexing".to_string()); }
    if content.contains("search") { patterns.push("searching".to_string()); }
    if content.contains("git") { patterns.push("git_integration".to_string()); }
    if content.contains("parquet") { patterns.push("parquet".to_string()); }
    if content.contains("ZK") || content.contains("zk") { patterns.push("zero_knowledge".to_string()); }
    if content.contains("GPU") || content.contains("gpu") { patterns.push("gpu".to_string()); }
    if content.contains("first_bit") { patterns.push("bit_analysis".to_string()); }
    if content.contains("semantic") { patterns.push("semantic".to_string()); }
    if content.contains("predict") { patterns.push("prediction".to_string()); }

    Some(SearchTool {
        path: path.to_path_buf(),
        name: path.file_name()?.to_string_lossy().to_string(),
        lines,
        functions,
        structs,
        complexity,
        shard,
        common_patterns: patterns,
    })
}

fn find_search_tools(base: &Path) -> Vec<PathBuf> {
    let search_keywords = [
        "search", "index", "find", "grep", "query",
        "cache", "memory", "storage", "tier", "overlay"
    ];

    WalkDir::new(base)
        .max_depth(5)
        .into_iter()
        .filter_map(|e| e.ok())
        .filter(|e| {
            e.path().extension().map_or(false, |ext| ext == "rs") &&
            e.path().to_string_lossy().contains("/bin/") &&
            search_keywords.iter().any(|kw| 
                e.path().file_name()
                    .and_then(|n| n.to_str())
                    .map_or(false, |n| n.to_lowercase().contains(kw))
            )
        })
        .map(|e| e.path().to_path_buf())
        .collect()
}

fn generate_knuth_literate_doc(lattice: &ComplexityLattice) -> String {
    let mut doc = String::new();
    
    doc.push_str("% SEARCH TOOLS LATTICE: A Literate Analysis\n");
    doc.push_str("% In the style of Donald E. Knuth\n\n");
    
    doc.push_str("\\section{Introduction}\n\n");
    doc.push_str(&format!("We have discovered {} search tools in our codebase. ", lattice.total_tools));
    doc.push_str("Each tool represents a different approach to the fundamental problem of ");
    doc.push_str("finding information quickly.\n\n");
    
    doc.push_str("\\section{The Monster Lattice}\n\n");
    doc.push_str("We shard these tools by complexity modulo 71, the largest Monster prime. ");
    doc.push_str("This creates a natural lattice structure where tools of similar complexity ");
    doc.push_str("cluster together.\n\n");
    
    doc.push_str("\\subsection{Shard Distribution}\n\n");
    doc.push_str("\\begin{verbatim}\n");
    for (shard_num, tools) in lattice.shards.iter().enumerate() {
        if !tools.is_empty() {
            doc.push_str(&format!("Shard {}: {} tools\n", shard_num, tools.len()));
        }
    }
    doc.push_str("\\end{verbatim}\n\n");
    
    doc.push_str("\\section{Common Patterns}\n\n");
    doc.push_str("The following patterns emerge across multiple tools:\n\n");
    doc.push_str("\\begin{itemize}\n");
    
    let mut pattern_counts: HashMap<String, usize> = HashMap::new();
    for shard in &lattice.shards {
        for tool in shard {
            for pattern in &tool.common_patterns {
                *pattern_counts.entry(pattern.clone()).or_insert(0) += 1;
            }
        }
    }
    
    let mut patterns: Vec<_> = pattern_counts.into_iter().collect();
    patterns.sort_by(|a, b| b.1.cmp(&a.1));
    
    for (pattern, count) in patterns.iter().take(10) {
        doc.push_str(&format!("  \\item \\texttt{{{}}} appears in {} tools\n", pattern, count));
    }
    doc.push_str("\\end{itemize}\n\n");
    
    doc.push_str("\\section{Conclusion}\n\n");
    doc.push_str("The lattice structure reveals natural groupings and common patterns. ");
    doc.push_str("Future work should focus on extracting these patterns into reusable components.\n");
    
    doc
}

fn main() {
    let repo_root = std::env::args()
        .nth(1)
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from("."));

    println!("🔍 Knuth's Search Lattice Analysis");
    println!("===================================\n");
    println!("Repo: {}\n", repo_root.display());

    // Find all search tools
    println!("§0. Discovery Phase\n");
    let tool_paths = find_search_tools(&repo_root);
    println!("  Found {} search/index tools\n", tool_paths.len());

    // Build lattice
    let mut lattice = ComplexityLattice::new();
    
    for path in &tool_paths {
        if let Some(tool) = analyze_rust_file(path) {
            println!("  Analyzing: {} (complexity: {}, shard: {})", 
                tool.name, tool.complexity, tool.shard);
            lattice.add_tool(tool);
        }
    }

    // Analyze
    lattice.analyze();

    // Generate literate document
    println!("\n§5. Literate Programming Document\n");
    let doc = generate_knuth_literate_doc(&lattice);
    
    let doc_path = repo_root.join("KNUTH_SEARCH_LATTICE.tex");
    if let Err(e) = fs::write(&doc_path, doc) {
        eprintln!("  Error writing document: {}", e);
    } else {
        println!("  ✓ Written to: {}", doc_path.display());
    }

    println!("\n✅ Analysis complete!");
    println!("\n\"Premature optimization is the root of all evil.\" — Donald Knuth");
}
