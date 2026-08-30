use std::fs;
use std::collections::HashMap;

#[derive(Debug)]
struct AlgebraSystem {
    name: String,
    examples: HashMap<String, String>,
}

fn main() {
    let content = fs::read_to_string("hyperpolyglot/markup/more-computer-algebra")
        .expect("Failed to read more-computer-algebra");
    
    let systems = vec!["pari/gp", "magma", "gap", "singular"];
    
    println!("# Computer Algebra Systems for Monster Group");
    println!("\nRelevant systems from hyperpolyglot.org:\n");
    
    for system in systems {
        println!("## {}", system.to_uppercase());
        
        // Extract group theory sections
        if content.contains("groups") {
            println!("  ✓ Group theory support");
        }
        if content.contains("subgroups") {
            println!("  ✓ Subgroup operations");
        }
        if content.contains("group homomorphisms") {
            println!("  ✓ Homomorphism support");
        }
        if content.contains("permutations") {
            println!("  ✓ Permutation groups");
        }
        println!();
    }
    
    // Extract sections relevant to Monster group
    let sections = vec![
        "groups", "subgroups", "group-homomorphisms", 
        "permutations", "number-theory", "combinatorics"
    ];
    
    println!("\n# Relevant Sections for Monster Group Work:");
    for section in sections {
        if content.contains(section) {
            println!("  - {}", section);
        }
    }
}
