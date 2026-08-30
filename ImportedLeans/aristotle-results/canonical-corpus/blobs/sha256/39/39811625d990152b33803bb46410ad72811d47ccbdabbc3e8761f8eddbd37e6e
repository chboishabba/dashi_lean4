// LMFDB to Prolog Ingestion Tool
// Minimal implementation - ingests JSON, Parquet, and Markdown LMFDB files into Prolog facts

use polars::prelude::*;
use serde_json::Value;
use std::fs;
use std::io::Write;
use std::path::{Path, PathBuf};
use walkdir::WalkDir;

const MONSTER_PRIMES: [u64; 15] = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71];

#[derive(Debug)]
struct LmfdbFile {
    path: PathBuf,
    file_type: FileType,
    zone: u8,
}

#[derive(Debug)]
enum FileType {
    Json,
    Parquet,
    Markdown,
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("🔍 LMFDB to Prolog Ingestion");
    println!("━━━━━━━━━━━━━━━━━━━━━━━━━━━━");
    
    let base = Path::new("/home/mdupont/experiments/monster");
    let files = discover_lmfdb_files(base)?;
    
    println!("📁 Found {} LMFDB files", files.len());
    
    let mut prolog_out = fs::File::create("lmfdb_knowledge_base.pl")?;
    write_header(&mut prolog_out)?;
    
    for file in &files {
        println!("  Processing: {:?}", file.path.file_name().unwrap());
        match file.file_type {
            FileType::Json => ingest_json(&file, &mut prolog_out)?,
            FileType::Parquet => ingest_parquet(&file, &mut prolog_out)?,
            FileType::Markdown => ingest_markdown(&file, &mut prolog_out)?,
        }
    }
    
    write_footer(&mut prolog_out, &files)?;
    
    println!("\n✅ Generated: lmfdb_knowledge_base.pl");
    Ok(())
}

fn discover_lmfdb_files(base: &Path) -> Result<Vec<LmfdbFile>, Box<dyn std::error::Error>> {
    let mut files = Vec::new();
    
    for entry in WalkDir::new(base)
        .max_depth(5)
        .into_iter()
        .filter_map(|e| e.ok())
        .filter(|e| e.file_type().is_file())
    {
        let path = entry.path();
        let path_str = path.to_string_lossy().to_lowercase();
        
        if !path_str.contains("lmfdb") {
            continue;
        }
        
        let file_type = match path.extension().and_then(|s| s.to_str()) {
            Some("json") => FileType::Json,
            Some("parquet") => FileType::Parquet,
            Some("md") => FileType::Markdown,
            _ => continue,
        };
        
        let zone = assign_zone(path);
        
        files.push(LmfdbFile {
            path: path.to_path_buf(),
            file_type,
            zone,
        });
    }
    
    Ok(files)
}

fn assign_zone(path: &Path) -> u8 {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};
    
    let mut hasher = DefaultHasher::new();
    path.to_string_lossy().hash(&mut hasher);
    (hasher.finish() % 71) as u8
}

fn write_header(out: &mut fs::File) -> Result<(), Box<dyn std::error::Error>> {
    writeln!(out, "% LMFDB Knowledge Base - Auto-generated")?;
    writeln!(out, "% Generated: {}", chrono::Local::now())?;
    writeln!(out, "%")?;
    writeln!(out, "% Predicates:")?;
    writeln!(out, "%   lmfdb_file(Path, Type, Zone)")?;
    writeln!(out, "%   lmfdb_object(ID, Type, Properties)")?;
    writeln!(out, "%   lmfdb_property(ObjectID, Key, Value)")?;
    writeln!(out, "%   lmfdb_prime(ObjectID, Prime)")?;
    writeln!(out, "%   lmfdb_zone(Zone, Count)")?;
    writeln!(out)?;
    
    writeln!(out, ":- module(lmfdb_kb, [")?;
    writeln!(out, "    lmfdb_file/3,")?;
    writeln!(out, "    lmfdb_object/3,")?;
    writeln!(out, "    lmfdb_property/3,")?;
    writeln!(out, "    lmfdb_prime/2,")?;
    writeln!(out, "    lmfdb_zone/2")?;
    writeln!(out, "]).")?;
    writeln!(out)?;
    
    writeln!(out, "% Monster primes")?;
    for prime in &MONSTER_PRIMES {
        writeln!(out, "monster_prime({}).", prime)?;
    }
    writeln!(out)?;
    
    Ok(())
}

fn ingest_json(file: &LmfdbFile, out: &mut fs::File) -> Result<(), Box<dyn std::error::Error>> {
    let content = fs::read_to_string(&file.path)?;
    let json: Value = serde_json::from_str(&content)?;
    
    let file_name = file.path.file_name().unwrap().to_string_lossy();
    writeln!(out, "% JSON: {}", file_name)?;
    writeln!(out, "lmfdb_file('{}', json, {}).", file.path.display(), file.zone)?;
    
    match &json {
        Value::Object(map) => {
            for (key, value) in map {
                write_json_fact(out, &file_name, key, value)?;
            }
        }
        Value::Array(arr) => {
            for (idx, item) in arr.iter().enumerate() {
                let id = format!("{}_{}", file_name, idx);
                write_json_object(out, &id, item)?;
            }
        }
        _ => {}
    }
    
    writeln!(out)?;
    Ok(())
}

fn write_json_fact(out: &mut fs::File, parent: &str, key: &str, value: &Value) -> Result<(), Box<dyn std::error::Error>> {
    let safe_key = sanitize_atom(key);
    let safe_parent = sanitize_atom(parent);
    
    match value {
        Value::Number(n) => {
            writeln!(out, "lmfdb_property('{}', {}, {}).", safe_parent, safe_key, n)?;
        }
        Value::String(s) => {
            let safe_val = sanitize_string(s);
            writeln!(out, "lmfdb_property('{}', {}, '{}').", safe_parent, safe_key, safe_val)?;
        }
        Value::Bool(b) => {
            writeln!(out, "lmfdb_property('{}', {}, {}).", safe_parent, safe_key, b)?;
        }
        _ => {}
    }
    
    Ok(())
}

fn write_json_object(out: &mut fs::File, id: &str, obj: &Value) -> Result<(), Box<dyn std::error::Error>> {
    let safe_id = sanitize_atom(id);
    
    if let Value::Object(map) = obj {
        writeln!(out, "lmfdb_object('{}', json_object, []).", safe_id)?;
        
        for (key, value) in map {
            write_json_fact(out, &safe_id, key, value)?;
        }
    }
    
    Ok(())
}

fn ingest_parquet(file: &LmfdbFile, out: &mut fs::File) -> Result<(), Box<dyn std::error::Error>> {
    let file_name = file.path.file_name().unwrap().to_string_lossy();
    writeln!(out, "% Parquet: {}", file_name)?;
    writeln!(out, "lmfdb_file('{}', parquet, {}).", file.path.display(), file.zone)?;
    
    let df = ParquetReader::new(fs::File::open(&file.path)?)
        .finish()?;
    
    let rows = df.height().min(100); // Limit to 100 rows
    
    for i in 0..rows {
        let id = format!("{}_{}", sanitize_atom(&file_name), i);
        writeln!(out, "lmfdb_object('{}', parquet_row, []).", id)?;
        
        for col in df.get_columns() {
            let col_name = col.name();
            if let Ok(val) = col.get(i) {
                let val_str = format!("{}", val);
                writeln!(out, "lmfdb_property('{}', {}, '{}').", 
                         id, sanitize_atom(col_name), sanitize_string(&val_str))?;
            }
        }
    }
    
    writeln!(out)?;
    Ok(())
}

fn ingest_markdown(file: &LmfdbFile, out: &mut fs::File) -> Result<(), Box<dyn std::error::Error>> {
    let file_name = file.path.file_name().unwrap().to_string_lossy();
    writeln!(out, "% Markdown: {}", file_name)?;
    writeln!(out, "lmfdb_file('{}', markdown, {}).", file.path.display(), file.zone)?;
    
    let content = fs::read_to_string(&file.path)?;
    let lines: Vec<&str> = content.lines().take(50).collect();
    
    let id = sanitize_atom(&file_name);
    writeln!(out, "lmfdb_object('{}', markdown_doc, []).", id)?;
    
    for (idx, line) in lines.iter().enumerate() {
        if line.trim().is_empty() {
            continue;
        }
        let safe_line = sanitize_string(line);
        writeln!(out, "lmfdb_property('{}', line_{}, '{}').", id, idx, safe_line)?;
    }
    
    writeln!(out)?;
    Ok(())
}

fn write_footer(out: &mut fs::File, files: &[LmfdbFile]) -> Result<(), Box<dyn std::error::Error>> {
    writeln!(out, "% Statistics")?;
    
    let mut zone_counts = vec![0u32; 71];
    for file in files {
        zone_counts[file.zone as usize] += 1;
    }
    
    for (zone, count) in zone_counts.iter().enumerate() {
        if *count > 0 {
            writeln!(out, "lmfdb_zone({}, {}).", zone, count)?;
        }
    }
    
    writeln!(out)?;
    writeln!(out, "% Total files: {}", files.len())?;
    
    Ok(())
}

fn sanitize_atom(s: &str) -> String {
    s.chars()
        .map(|c| if c.is_alphanumeric() || c == '_' { c } else { '_' })
        .collect()
}

fn sanitize_string(s: &str) -> String {
    s.replace('\'', "\\'")
        .replace('\\', "\\\\")
        .chars()
        .take(200)
        .collect()
}
