// Syn Code Ingestion: Parse all Rust code into Monster lattice
// Uses syn to extract AST, analyze complexity, shard by 71

use std::collections::HashMap;
use std::fs;
use std::path::{Path, PathBuf};
use syn::{
    visit::Visit, File, Item, ItemFn, ItemStruct, ItemEnum, ItemImpl,
    Expr, Stmt, Type, Pat, Block, Attribute
};
use walkdir::WalkDir;
use serde::{Serialize, Deserialize};

#[derive(Debug, Clone, Serialize, Deserialize)]
struct RustCodeAnalysis {
    file: PathBuf,
    functions: Vec<FunctionInfo>,
    structs: Vec<StructInfo>,
    enums: Vec<EnumInfo>,
    impls: Vec<ImplInfo>,
    complexity: ComplexityMetrics,
    shard: u8,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct FunctionInfo {
    name: String,
    line: usize,
    params: usize,
    return_type: String,
    statements: usize,
    cyclomatic: usize,
    attributes: Vec<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct StructInfo {
    name: String,
    line: usize,
    fields: usize,
    generics: usize,
    attributes: Vec<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct EnumInfo {
    name: String,
    line: usize,
    variants: usize,
    attributes: Vec<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct ImplInfo {
    type_name: String,
    line: usize,
    methods: usize,
    trait_impl: Option<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct ComplexityMetrics {
    lines: usize,
    functions: usize,
    structs: usize,
    enums: usize,
    impls: usize,
    total_statements: usize,
    total_cyclomatic: usize,
    monster_score: u64,
}

struct SynVisitor {
    file_path: PathBuf,
    functions: Vec<FunctionInfo>,
    structs: Vec<StructInfo>,
    enums: Vec<EnumInfo>,
    impls: Vec<ImplInfo>,
    current_cyclomatic: usize,
    current_statements: usize,
}

impl SynVisitor {
    fn new(file_path: PathBuf) -> Self {
        Self {
            file_path,
            functions: Vec::new(),
            structs: Vec::new(),
            enums: Vec::new(),
            impls: Vec::new(),
            current_cyclomatic: 1,
            current_statements: 0,
        }
    }

    fn extract_attributes(attrs: &[Attribute]) -> Vec<String> {
        attrs.iter()
            .filter_map(|attr| attr.path().get_ident().map(|i| i.to_string()))
            .collect()
    }
}

impl<'ast> Visit<'ast> for SynVisitor {
    fn visit_item_fn(&mut self, node: &'ast ItemFn) {
        let name = node.sig.ident.to_string();
        let line = node.sig.ident.span().start().line;
        let params = node.sig.inputs.len();
        let return_type = match &node.sig.output {
            syn::ReturnType::Default => "()".to_string(),
            syn::ReturnType::Type(_, ty) => quote::quote!(#ty).to_string(),
        };
        
        // Reset counters
        self.current_cyclomatic = 1;
        self.current_statements = 0;
        
        // Visit function body
        self.visit_block(&node.block);
        
        let attributes = Self::extract_attributes(&node.attrs);
        
        self.functions.push(FunctionInfo {
            name,
            line,
            params,
            return_type,
            statements: self.current_statements,
            cyclomatic: self.current_cyclomatic,
            attributes,
        });
        
        syn::visit::visit_item_fn(self, node);
    }

    fn visit_item_struct(&mut self, node: &'ast ItemStruct) {
        let name = node.ident.to_string();
        let line = node.ident.span().start().line;
        let fields = match &node.fields {
            syn::Fields::Named(f) => f.named.len(),
            syn::Fields::Unnamed(f) => f.unnamed.len(),
            syn::Fields::Unit => 0,
        };
        let generics = node.generics.params.len();
        let attributes = Self::extract_attributes(&node.attrs);
        
        self.structs.push(StructInfo {
            name,
            line,
            fields,
            generics,
            attributes,
        });
        
        syn::visit::visit_item_struct(self, node);
    }

    fn visit_item_enum(&mut self, node: &'ast ItemEnum) {
        let name = node.ident.to_string();
        let line = node.ident.span().start().line;
        let variants = node.variants.len();
        let attributes = Self::extract_attributes(&node.attrs);
        
        self.enums.push(EnumInfo {
            name,
            line,
            variants,
            attributes,
        });
        
        syn::visit::visit_item_enum(self, node);
    }

    fn visit_item_impl(&mut self, node: &'ast ItemImpl) {
        let type_name = quote::quote!(#node.self_ty).to_string();
        let line = node.impl_token.span.start().line;
        let methods = node.items.len();
        let trait_impl = node.trait_.as_ref().map(|(_, path, _)| {
            quote::quote!(#path).to_string()
        });
        
        self.impls.push(ImplInfo {
            type_name,
            line,
            methods,
            trait_impl,
        });
        
        syn::visit::visit_item_impl(self, node);
    }

    fn visit_stmt(&mut self, node: &'ast Stmt) {
        self.current_statements += 1;
        syn::visit::visit_stmt(self, node);
    }

    fn visit_expr(&mut self, node: &'ast Expr) {
        // Count cyclomatic complexity
        match node {
            Expr::If(_) | Expr::Match(_) | Expr::While(_) | Expr::ForLoop(_) => {
                self.current_cyclomatic += 1;
            }
            Expr::Binary(expr) => {
                if matches!(expr.op, syn::BinOp::And(_) | syn::BinOp::Or(_)) {
                    self.current_cyclomatic += 1;
                }
            }
            _ => {}
        }
        syn::visit::visit_expr(self, node);
    }
}

fn analyze_rust_file(path: &Path) -> Option<RustCodeAnalysis> {
    let content = fs::read_to_string(path).ok()?;
    let lines = content.lines().count();
    
    let syntax = syn::parse_file(&content).ok()?;
    
    let mut visitor = SynVisitor::new(path.to_path_buf());
    visitor.visit_file(&syntax);
    
    let total_statements: usize = visitor.functions.iter().map(|f| f.statements).sum();
    let total_cyclomatic: usize = visitor.functions.iter().map(|f| f.cyclomatic).sum();
    
    // Monster score: lines + 10*functions + 5*structs + 3*enums + cyclomatic
    let monster_score = lines as u64
        + 10 * visitor.functions.len() as u64
        + 5 * visitor.structs.len() as u64
        + 3 * visitor.enums.len() as u64
        + total_cyclomatic as u64;
    
    let shard = (monster_score % 71) as u8;
    
    Some(RustCodeAnalysis {
        file: path.to_path_buf(),
        functions: visitor.functions,
        structs: visitor.structs,
        enums: visitor.enums,
        impls: visitor.impls,
        complexity: ComplexityMetrics {
            lines,
            functions: visitor.functions.len(),
            structs: visitor.structs.len(),
            enums: visitor.enums.len(),
            impls: visitor.impls.len(),
            total_statements,
            total_cyclomatic,
            monster_score,
        },
        shard,
    })
}

fn ingest_all_rust_code(base_path: &Path) -> Vec<RustCodeAnalysis> {
    println!("🦀 Ingesting all Rust code with syn");
    println!("====================================\n");
    println!("Base path: {}\n", base_path.display());
    
    let mut analyses = Vec::new();
    let mut file_count = 0;
    
    for entry in WalkDir::new(base_path)
        .max_depth(10)
        .into_iter()
        .filter_map(|e| e.ok())
        .filter(|e| e.path().extension().and_then(|s| s.to_str()) == Some("rs"))
    {
        file_count += 1;
        if file_count % 100 == 0 {
            println!("  Processed {} files...", file_count);
        }
        
        if let Some(analysis) = analyze_rust_file(entry.path()) {
            analyses.push(analysis);
        }
    }
    
    println!("\n✓ Analyzed {} Rust files", analyses.len());
    analyses
}

fn generate_shard_report(analyses: &[RustCodeAnalysis]) {
    println!("\n📊 Shard Distribution (by Monster prime 71)");
    println!("============================================\n");
    
    let mut shard_counts: HashMap<u8, usize> = HashMap::new();
    let mut shard_complexity: HashMap<u8, u64> = HashMap::new();
    
    for analysis in analyses {
        *shard_counts.entry(analysis.shard).or_insert(0) += 1;
        *shard_complexity.entry(analysis.shard).or_insert(0) += analysis.complexity.monster_score;
    }
    
    let mut shards: Vec<_> = shard_counts.keys().collect();
    shards.sort();
    
    for shard in shards {
        let count = shard_counts[shard];
        let complexity = shard_complexity[shard];
        let avg = complexity / count as u64;
        println!("  Shard {:2}: {:4} files, total complexity: {:8}, avg: {:6}", 
            shard, count, complexity, avg);
    }
}

fn generate_complexity_report(analyses: &[RustCodeAnalysis]) {
    println!("\n📈 Complexity Metrics");
    println!("====================\n");
    
    let total_lines: usize = analyses.iter().map(|a| a.complexity.lines).sum();
    let total_functions: usize = analyses.iter().map(|a| a.complexity.functions).sum();
    let total_structs: usize = analyses.iter().map(|a| a.complexity.structs).sum();
    let total_enums: usize = analyses.iter().map(|a| a.complexity.enums).sum();
    let total_impls: usize = analyses.iter().map(|a| a.complexity.impls).sum();
    let total_cyclomatic: usize = analyses.iter().map(|a| a.complexity.total_cyclomatic).sum();
    let total_monster_score: u64 = analyses.iter().map(|a| a.complexity.monster_score).sum();
    
    println!("  Total files:       {}", analyses.len());
    println!("  Total lines:       {}", total_lines);
    println!("  Total functions:   {}", total_functions);
    println!("  Total structs:     {}", total_structs);
    println!("  Total enums:       {}", total_enums);
    println!("  Total impls:       {}", total_impls);
    println!("  Total cyclomatic:  {}", total_cyclomatic);
    println!("  Total Monster score: {}", total_monster_score);
    println!("  Avg Monster score: {}", total_monster_score / analyses.len() as u64);
}

fn find_monster_patterns(analyses: &[RustCodeAnalysis]) {
    println!("\n🔍 Monster Patterns");
    println!("===================\n");
    
    // Find files with Monster prime counts
    let monster_primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71];
    
    for prime in monster_primes {
        let matches: Vec<_> = analyses.iter()
            .filter(|a| a.complexity.functions == prime)
            .collect();
        
        if !matches.is_empty() {
            println!("  Files with exactly {} functions: {}", prime, matches.len());
        }
    }
}

fn main() {
    let base_path = std::env::args()
        .nth(1)
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from("."));
    
    let analyses = ingest_all_rust_code(&base_path);
    
    generate_shard_report(&analyses);
    generate_complexity_report(&analyses);
    find_monster_patterns(&analyses);
    
    // Save to JSON
    println!("\n💾 Saving analysis...");
    let json = serde_json::to_string_pretty(&analyses).unwrap();
    fs::write("rust_syn_analysis.json", json).unwrap();
    println!("✓ Saved to rust_syn_analysis.json");
    
    // Save to parquet
    println!("\n💾 Saving to parquet...");
    // TODO: Convert to parquet format
    
    println!("\n✅ Syn ingestion complete!");
}
