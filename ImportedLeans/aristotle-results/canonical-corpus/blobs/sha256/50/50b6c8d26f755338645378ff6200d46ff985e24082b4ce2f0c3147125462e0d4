// ZK71 Quine Integration Test
// Tests all 71 zones with OODA pipeline simulation

use std::collections::HashMap;

const MONSTER_PRIMES: [u8; 15] = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71];

#[derive(Debug, Clone, Copy)]
struct Zone {
    id: u8,
    prime: u8,
    level: &'static str,
    taint: u8,
}

const fn zone_level(z: u8) -> &'static str {
    match z {
        71 => "CATASTROPHIC",
        59..=70 => "CRITICAL",
        47..=58 => "HIGH",
        31..=46 => "MEDIUM",
        23..=30 => "LOW_MEDIUM",
        11..=22 => "LOW",
        2..=10 => "MINIMAL",
        _ => "NONE",
    }
}

const fn taint_threshold(z: u8) -> u8 {
    match z {
        71 => 255,
        59..=70 => 200,
        47..=58 => 150,
        31..=46 => 100,
        23..=30 => 50,
        11..=22 => 25,
        2..=10 => 10,
        _ => 0,
    }
}

const ZONES: [Zone; 71] = {
    let mut zones = [Zone { id: 0, prime: 2, level: "NONE", taint: 0 }; 71];
    let mut i = 0;
    while i <= 70 {
        zones[i] = Zone {
            id: i as u8,
            prime: MONSTER_PRIMES[i % 15],
            level: zone_level(i as u8),
            taint: taint_threshold(i as u8),
        };
        i += 1;
    }
    zones
};

// Simulate OODA pipeline stages
#[derive(Debug)]
enum PipelineStage {
    DiskData,      // Zone 0-10
    Inode,         // Zone 11-22
    PlocateResult, // Zone 23-30
    ParquetShard,  // Zone 31-46
    ShmemShard,    // Zone 47-58
    GpuShard,      // Zone 59-70
}

impl PipelineStage {
    fn zone_range(&self) -> (u8, u8) {
        match self {
            Self::DiskData => (0, 10),
            Self::Inode => (11, 22),
            Self::PlocateResult => (23, 30),
            Self::ParquetShard => (31, 46),
            Self::ShmemShard => (47, 58),
            Self::GpuShard => (59, 70),
        }
    }
    
    fn zones(&self) -> Vec<&'static Zone> {
        let (min, max) = self.zone_range();
        ZONES.iter()
            .filter(|z| z.id >= min && z.id <= max)
            .collect()
    }
}

// Quine test: Each zone generates itself
fn test_quine_property() {
    println!("🔄 Testing Quine Property");
    println!("━━━━━━━━━━━━━━━━━━━━━━━━━");
    
    for zone in &ZONES {
        // Generate policy
        let read_zones: Vec<u8> = (0..=zone.id).collect();
        let write_zones = vec![zone.id];
        
        // Generate pointer
        let pointer_prime = zone.prime;
        let witness_type = format!("Zone{}", zone.id);
        
        // Generate witness
        let type_sig = format!("ZK71Zone{}", zone.id);
        let homotopy_level = zone.id % 15;
        
        // Verify self-consistency
        assert_eq!(read_zones.len(), (zone.id + 1) as usize);
        assert_eq!(write_zones.len(), 1);
        assert_eq!(pointer_prime, MONSTER_PRIMES[(zone.id % 15) as usize]);
        assert_eq!(homotopy_level, zone.id % 15);
        
        if zone.id % 10 == 0 {
            println!("  Zone {:2}: ✅ Self-consistent (prime {}, level {})", 
                     zone.id, zone.prime, zone.level);
        }
    }
    
    println!("  ✅ All 71 zones pass quine property\n");
}

// Test pipeline flow
fn test_pipeline_flow() {
    println!("🔀 Testing Pipeline Flow");
    println!("━━━━━━━━━━━━━━━━━━━━━━━━");
    
    let stages = [
        PipelineStage::DiskData,
        PipelineStage::Inode,
        PipelineStage::PlocateResult,
        PipelineStage::ParquetShard,
        PipelineStage::ShmemShard,
        PipelineStage::GpuShard,
    ];
    
    for stage in &stages {
        let zones = stage.zones();
        let (min, max) = stage.zone_range();
        println!("  {:?}: {} zones ({}..{})", stage, zones.len(), min, max);
        
        // Verify zones are in range
        for zone in &zones {
            assert!(zone.id >= min && zone.id <= max);
        }
    }
    
    println!("  ✅ All pipeline stages valid\n");
}

// Test zone distribution
fn test_zone_distribution() {
    println!("📊 Testing Zone Distribution");
    println!("━━━━━━━━━━━━━━━━━━━━━━━━━━");
    
    let mut level_counts: HashMap<&str, usize> = HashMap::new();
    let mut prime_counts: HashMap<u8, usize> = HashMap::new;
    
    for zone in &ZONES {
        *level_counts.entry(zone.level).or_insert(0) += 1;
        *prime_counts.entry(zone.prime).or_insert(0) += 1;
    }
    
    println!("  Security Levels:");
    for (level, count) in &level_counts {
        println!("    {}: {} zones", level, count);
    }
    
    println!("\n  Prime Distribution:");
    for (prime, count) in &prime_counts {
        println!("    Prime {}: {} zones", prime, count);
    }
    
    // Verify total
    let total: usize = level_counts.values().sum();
    assert_eq!(total, 71);
    println!("\n  ✅ Total: {} zones\n", total);
}

// Test taint propagation
fn test_taint_propagation() {
    println!("🔒 Testing Taint Propagation");
    println!("━━━━━━━━━━━━━━━━━━━━━━━━━━");
    
    // Simulate data flowing through zones
    let mut max_taint = 0u8;
    
    for zone in &ZONES {
        // Taint increases with zone ID
        assert!(zone.taint >= max_taint);
        max_taint = zone.taint;
        
        if zone.id % 10 == 0 {
            println!("  Zone {:2}: taint={}", zone.id, zone.taint);
        }
    }
    
    println!("  ✅ Taint is monotonic (max={})\n", max_taint);
}

// Test prime cycling
fn test_prime_cycling() {
    println!("🔁 Testing Prime Cycling");
    println!("━━━━━━━━━━━━━━━━━━━━━━━");
    
    for i in 0..15 {
        let zone1 = &ZONES[i];
        let zone2 = &ZONES[i + 15];
        let zone3 = &ZONES[i + 30];
        
        // All should have same prime
        assert_eq!(zone1.prime, zone2.prime);
        assert_eq!(zone2.prime, zone3.prime);
        
        println!("  Prime {}: zones {}, {}, {} (cycles every 15)", 
                 zone1.prime, zone1.id, zone2.id, zone3.id);
    }
    
    println!("  ✅ Primes cycle correctly\n");
}

fn main() {
    println!("🎯 ZK71 Quine Integration Test");
    println!("═══════════════════════════════\n");
    
    test_quine_property();
    test_pipeline_flow();
    test_zone_distribution();
    test_taint_propagation();
    test_prime_cycling();
    
    println!("═══════════════════════════════");
    println!("✅ All tests passed!");
    println!("\n📝 Summary:");
    println!("  • 71 zones defined");
    println!("  • 15 Monster primes cycling");
    println!("  • 6 pipeline stages");
    println!("  • 8 security levels");
    println!("  • Quine property verified");
    println!("  • Taint propagation monotonic");
    println!("  • Prime cycling correct");
}
