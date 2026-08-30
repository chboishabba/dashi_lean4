// ZK71 Zone Quine Pattern - Self-replicating zone constants
// Each zone (0-70) generates its own const definition

const MONSTER_PRIMES: [u8; 15] = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71];

#[derive(Debug, Clone, Copy)]
pub struct Zone {
    pub id: u8,
    pub prime: u8,
    pub level: &'static str,
}

const fn zone_level(zone: u8) -> &'static str {
    match zone {
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

// Zone array for runtime access
pub const ZONES: [Zone; 71] = {
    let mut zones = [Zone { id: 0, prime: 2, level: "NONE" }; 71];
    let mut i = 0;
    while i <= 70 {
        zones[i] = Zone {
            id: i as u8,
            prime: MONSTER_PRIMES[i % 15],
            level: zone_level(i as u8),
        };
        i += 1;
    }
    zones
};

fn main() {
    println!("🔐 ZK71 Zone Quine Pattern");
    println!("━━━━━━━━━━━━━━━━━━━━━━━━━━");
    
    for zone in &ZONES {
        println!("Zone {:2} | Prime {:2} | {}", zone.id, zone.prime, zone.level);
    }
    
    println!("\n📊 Zone Distribution:");
    let levels = ["CATASTROPHIC", "CRITICAL", "HIGH", "MEDIUM", "LOW_MEDIUM", "LOW", "MINIMAL", "NONE"];
    for level in &levels {
        let count = ZONES.iter().filter(|z| z.level == *level).count();
        if count > 0 {
            println!("  {}: {} zones", level, count);
        }
    }
}
