// Multi-Axial Galois Ziggurat - Load-Bearing Architecture
// Not a ladder, but a branched stratified system
// Each prime p defines a p-local extension axis
// K_n ≈ ∏_{p|n, p||M|} K^(p)_{f_p(n)}
//
// Key insight: 71 is not "biggest" — it's COMPLETE
// All Monster-relevant prime directions activated

const MONSTER_PRIMES: [u64; 15] = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71];

#[derive(Debug, Clone)]
struct ComplexityVector {
    degree: u64,              // [K_n : ℚ]
    ramification: usize,      // #Ram(K_n)
    representation_dim: u64,  // dim V_n
    leech_height: u64,        // ht_Λ(n)
}

#[derive(Debug, Clone)]
struct PrimeAxis {
    prime: u64,
    max_level: u64,
    complexity_profile: Vec<u64>,  // f_p(n)
}

#[derive(Debug, Clone)]
struct GaloisLevel {
    level: u64,
    complexity: ComplexityVector,
    prime_sectors: Vec<(u64, u64)>,  // (prime, local_level)
    twisted_modules: Vec<u64>,        // V^♮_g for ord(g) ≤ n
}

#[derive(Debug)]
struct MultiAxialZiggurat {
    levels: Vec<GaloisLevel>,
    prime_axes: Vec<PrimeAxis>,
}

impl MultiAxialZiggurat {
    fn new() -> Self {
        let mut prime_axes = Vec::new();
        
        // Each Monster prime defines an axis
        for &prime in &MONSTER_PRIMES {
            let max_level = (71 / prime).max(1);
            let complexity_profile: Vec<u64> = (1..=max_level)
                .map(|l| l * prime)
                .collect();
            
            prime_axes.push(PrimeAxis {
                prime,
                max_level,
                complexity_profile,
            });
        }
        
        let mut levels = Vec::new();
        
        // Level 0: K₀ = ℚ (base field, vacuum)
        levels.push(GaloisLevel {
            level: 0,
            complexity: ComplexityVector {
                degree: 1,
                ramification: 0,
                representation_dim: 1,  // Trivial rep
                leech_height: 0,
            },
            prime_sectors: vec![],
            twisted_modules: vec![1],
        });
        
        // Level 1: Moonshine normalization (trivial ↔ 196,883)
        // This is the choice of vacuum that makes j-function integral
        levels.push(GaloisLevel {
            level: 1,
            complexity: ComplexityVector {
                degree: 2,
                ramification: 1,
                representation_dim: 196883,
                leech_height: 1,
            },
            prime_sectors: vec![(2, 1)],
            twisted_modules: vec![1, 196883],
        });
        
        // Levels 2-15: Activate each Monster prime (one per level)
        for (idx, &prime) in MONSTER_PRIMES.iter().enumerate().skip(1) {
            let level = (idx + 1) as u64;
            let prev = &levels[level as usize - 1];
            
            let degree = prev.complexity.degree.saturating_mul(prime);
            let ramification = prev.complexity.ramification + 1;
            let rep_dim = prev.complexity.representation_dim.saturating_add(prime * prime);
            
            let mut sectors = prev.prime_sectors.clone();
            sectors.push((prime, 1));
            
            let mut modules = prev.twisted_modules.clone();
            modules.push(rep_dim);
            
            levels.push(GaloisLevel {
                level,
                complexity: ComplexityVector {
                    degree,
                    ramification,
                    representation_dim: rep_dim,
                    leech_height: level,
                },
                prime_sectors: sectors,
                twisted_modules: modules,
            });
        }
        
        // Levels 16-71: Composite extensions (all primes activated)
        // No new ramification, just deepening existing axes
        for level in 16..=71u64 {
            let prev = &levels[level as usize - 1];
            let prime = MONSTER_PRIMES[((level - 1) % 15) as usize];
            
            let degree = prev.complexity.degree.saturating_mul(2);
            let ramification = prev.complexity.ramification;  // No new primes
            let rep_dim = prev.complexity.representation_dim.saturating_add(level * level);
            
            let mut sectors = prev.prime_sectors.clone();
            // Increment local level for this prime axis
            if let Some(pos) = sectors.iter().position(|(p, _)| *p == prime) {
                sectors[pos].1 += 1;
            }
            
            let mut modules = prev.twisted_modules.clone();
            modules.push(rep_dim);
            
            levels.push(GaloisLevel {
                level,
                complexity: ComplexityVector {
                    degree,
                    ramification,
                    representation_dim: rep_dim,
                    leech_height: level,
                },
                prime_sectors: sectors,
                twisted_modules: modules,
            });
        }
        
        MultiAxialZiggurat {
            levels,
            prime_axes,
        }
    }
    
    fn level(&self, n: u64) -> Option<&GaloisLevel> {
        self.levels.get(n as usize)
    }
    
    fn is_complete(&self, level: u64) -> bool {
        // Complete when all Monster primes activated
        if let Some(lvl) = self.level(level) {
            lvl.prime_sectors.len() == MONSTER_PRIMES.len()
        } else {
            false
        }
    }
    
    fn galois_decomposition(&self, level: u64) -> Vec<u64> {
        // V_n = ⊕_{σ ∈ Gal(K_n/K₀)} V_n^σ
        if let Some(lvl) = self.level(level) {
            lvl.twisted_modules.clone()
        } else {
            vec![]
        }
    }
}

// Generate Prolog facts
fn generate_prolog(ziggurat: &MultiAxialZiggurat) -> String {
    let mut prolog = String::new();
    
    prolog.push_str("% Multi-Axial Galois Ziggurat\n");
    prolog.push_str("% A ziggurat is not climbed — it is resolved layer by layer\n\n");
    
    prolog.push_str(":- module(galois_ziggurat, [\n");
    prolog.push_str("    galois_level/5,\n");
    prolog.push_str("    prime_axis/3,\n");
    prolog.push_str("    complexity_vector/5,\n");
    prolog.push_str("    is_complete/1,\n");
    prolog.push_str("    twisted_module/2\n");
    prolog.push_str("]).\n\n");
    
    // Prime axes
    prolog.push_str("% Prime axes (15 Monster primes)\n");
    for axis in &ziggurat.prime_axes {
        prolog.push_str(&format!(
            "prime_axis({}, {}, {:?}).\n",
            axis.prime, axis.max_level, axis.complexity_profile
        ));
    }
    
    prolog.push_str("\n% Galois levels\n");
    for lvl in &ziggurat.levels {
        prolog.push_str(&format!(
            "galois_level({}, {}, {}, {}, {:?}).\n",
            lvl.level,
            lvl.complexity.degree,
            lvl.complexity.ramification,
            lvl.complexity.representation_dim,
            lvl.prime_sectors
        ));
        
        prolog.push_str(&format!(
            "complexity_vector({}, {}, {}, {}, {}).\n",
            lvl.level,
            lvl.complexity.degree,
            lvl.complexity.ramification,
            lvl.complexity.representation_dim,
            lvl.complexity.leech_height
        ));
    }
    
    prolog.push_str("\n% Completeness (all primes activated)\n");
    for lvl in &ziggurat.levels {
        if lvl.prime_sectors.len() == MONSTER_PRIMES.len() {
            prolog.push_str(&format!("is_complete({}).\n", lvl.level));
        }
    }
    
    prolog.push_str("\n% Twisted modules V^♮_g\n");
    for lvl in &ziggurat.levels {
        for &dim in &lvl.twisted_modules {
            prolog.push_str(&format!("twisted_module({}, {}).\n", lvl.level, dim));
        }
    }
    
    prolog.push_str("\n% Moonshine normalization\n");
    prolog.push_str("moonshine_vacuum(1, 196883).  % trivial ↔ first irrep\n");
    
    prolog.push_str("\n% K₇₁ is capstone (not apex)\n");
    prolog.push_str("capstone(71).  % All Monster data rationally visible\n");
    
    prolog
}

fn main() {
    println!("🏛️  Multi-Axial Galois Ziggurat");
    println!("═══════════════════════════════════════");
    println!("Load-bearing mathematical architecture\n");
    
    let ziggurat = MultiAxialZiggurat::new();
    
    println!("📐 Structure:");
    println!("  Base: K₀ = ℚ (rationals, vacuum)");
    println!("  Level 1: Moonshine normalization (1 ↔ 196,883)");
    println!("  Levels 2-15: Activate each Monster prime");
    println!("  Levels 16-71: Deepen existing axes\n");
    
    println!("🔱 Prime Axes (15 directions):");
    for axis in &ziggurat.prime_axes {
        println!("  p={:2}: max_level={}, profile={:?}", 
                 axis.prime, axis.max_level, 
                 &axis.complexity_profile[..axis.complexity_profile.len().min(3)]);
    }
    
    println!("\n📊 Key Levels:");
    for &n in &[0, 1, 2, 15, 71] {
        if let Some(lvl) = ziggurat.level(n) {
            println!("  K_{:2}: degree={}, ram={}, dim={}, sectors={}",
                     n, lvl.complexity.degree, lvl.complexity.ramification,
                     lvl.complexity.representation_dim, lvl.prime_sectors.len());
        }
    }
    
    println!("\n✅ Completeness:");
    println!("  Level 15: {} (all primes activated)", ziggurat.is_complete(15));
    println!("  Level 71: {} (capstone)", ziggurat.is_complete(71));
    
    println!("\n🎵 Galois Decomposition (first 3 levels):");
    for level in 0..=2 {
        let modules = ziggurat.galois_decomposition(level);
        println!("  K_{}: V = {:?}", level, modules);
    }
    
    // Generate Prolog
    let prolog = generate_prolog(&ziggurat);
    std::fs::write("prolog/galois_ziggurat.pl", prolog).unwrap();
    
    println!("\n✅ Generated: prolog/galois_ziggurat.pl");
    
    println!("\n🏛️  The Edifice:");
    println!("  • Multi-axial (not linear)");
    println!("  • 15 prime directions");
    println!("  • 71 levels (complete at 15, capstone at 71)");
    println!("  • Moonshine as boundary condition");
    println!("  • K₇₁: smallest field where all Monster data is rationally visible");
    println!("\n  \"A ziggurat is not climbed — it is resolved layer by layer.\"");
}
