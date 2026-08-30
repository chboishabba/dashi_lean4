# Hyperpolyglot Integration

## Overview

The [hyperpolyglot.org](https://hyperpolyglot.org) repository has been integrated as a submodule to provide comprehensive reference documentation for computer algebra systems relevant to Monster group research.

## Repository

- **Source**: https://github.com/clarkgrubb/hyperpolyglot
- **Location**: `./hyperpolyglot/`
- **Added**: 2026-01-30

## Relevant Files

### Computer Algebra Systems

1. **`markup/more-computer-algebra`** - PARI/GP, Magma, GAP, Singular
   - 69 group theory operations
   - 31 subgroup computations
   - 18 permutation group operations
   - 29 prime number operations
   - 42 group order computations
   - 5 elliptic curve operations

2. **`markup/computer-algebra`** - Mathematica, SymPy, Sage, Maxima
   - General symbolic computation
   - 4 permutation group operations
   - 2 number theory operations

3. **`markup/computer-algebra2`** - Extended algebra systems
   - 79 prime number operations
   - 31 factorial/combinatorics operations
   - 21 permutation group operations
   - 34 group order computations

## Monster Group Relevant Concepts

### Core Operations Needed

1. **Group Theory**
   - Group construction and representation
   - Subgroup lattices
   - Group homomorphisms
   - Character theory

2. **Prime Factorization**
   - Prime testing (isprime, IsPrime)
   - Prime factors (factor, PrimeDivisors)
   - Next/previous prime
   - nth prime

3. **Modular Arithmetic**
   - Chinese remainder theorem
   - Multiplicative order
   - Primitive roots
   - Discrete logarithm

4. **Permutation Groups**
   - Permutation construction
   - Order computation
   - Cycle decomposition
   - Group actions

## Recommended Systems for Monster Work

### 1. GAP (Groups, Algorithms, Programming)
- **Best for**: Group theory and permutation groups
- **Monster primes**: All 15 primes supported
- **Key functions**:
  - `SymmetricGroup(n)` - Symmetric groups
  - `Order(g)` - Group order
  - `Subgroups(g)` - Subgroup lattice
  - `FactorsInt(n)` - Prime factorization

### 2. PARI/GP
- **Best for**: Number theory and prime factorization
- **Monster primes**: Optimized for large primes
- **Key functions**:
  - `factor(n)` - Prime factorization
  - `isprime(n)` - Primality testing
  - `znorder(Mod(a,n))` - Multiplicative order
  - `chinese(Mod(a,m), Mod(b,n))` - CRT

### 3. Magma
- **Best for**: Advanced group computations
- **Monster primes**: Full support
- **Key functions**:
  - `Sym(n)` - Symmetric groups
  - `Order(g)` - Element order
  - `PrimeDivisors(n)` - Prime factors
  - `NumberOfSmallGroups(n)` - Group enumeration

### 4. Sage
- **Best for**: Unified interface to all systems
- **Monster primes**: Integrates GAP, PARI, Magma
- **Key advantage**: Python interface for scripting

## Integration with Monster Project

### Current Usage

The hyperpolyglot reference is used to:

1. **Verify implementations** - Compare Rust implementations against standard CAS
2. **Algorithm discovery** - Find efficient algorithms for group operations
3. **Cross-validation** - Test Monster Walk results across multiple systems
4. **Documentation** - Reference syntax for different systems

### Example: Prime Factorization

```rust
// Monster order factorization
// 2^46 × 3^20 × 5^9 × 7^6 × 11^2 × 13^3 × 17 × 19 × 23 × 29 × 31 × 41 × 47 × 59 × 71

// PARI/GP equivalent:
// factor(808017424794512875886459904961710757005754368000000000)

// GAP equivalent:
// FactorsInt(808017424794512875886459904961710757005754368000000000);

// Magma equivalent:
// PrimeDivisors(808017424794512875886459904961710757005754368000000000);
```

### Example: Group Order

```rust
// Computing order of permutation in Monster group

// GAP:
// g := (1,2,3,4,5);
// Order(g);  // Returns 5

// Magma:
// S5 := Sym(5);
// Order(S5!(1,2,3,4,5));  // Returns 5

// PARI/GP:
// Uses different representation for permutations
```

## Monster Primes Coverage

All 15 Monster primes are well-supported across systems:

| Prime | PARI/GP | Magma | GAP | Singular |
|-------|---------|-------|-----|----------|
| 2     | ✓       | ✓     | ✓   | ✓        |
| 3     | ✓       | ✓     | ✓   | ✓        |
| 5     | ✓       | ✓     | ✓   | ✓        |
| 7     | ✓       | ✓     | ✓   | ✓        |
| 11    | ✓       | ✓     | ✓   | ✓        |
| 13    | ✓       | ✓     | ✓   | ✓        |
| 17    | ✓       | ✓     | ✓   | ✓        |
| 19    | ✓       | ✓     | ✓   | ✓        |
| 23    | ✓       | ✓     | ✓   | ✓        |
| 29    | ✓       | ✓     | ✓   | ✓        |
| 31    | ✓       | ✓     | ✓   | ✓        |
| 41    | ✓       | ✓     | ✓   | ✓        |
| 47    | ✓       | ✓     | ✓   | ✓        |
| 59    | ✓       | ✓     | ✓   | ✓        |
| 71    | ✓       | ✓     | ✓   | ✓        |

## Key Findings from Hyperpolyglot

### Group Theory Operations (69 occurrences)
- Symmetric groups
- Cyclic groups
- Permutation groups
- Group actions
- Subgroup lattices

### Prime Operations (29 occurrences)
- `isprime(n)` / `IsPrime(n)` - Primality testing
- `factor(n)` / `PrimeDivisors(n)` - Factorization
- `nextprime(n)` / `NextPrime(n)` - Next prime
- `primes(n)` / `NthPrime(n)` - nth prime

### Modular Arithmetic
- Chinese Remainder Theorem
- Multiplicative order (znorder)
- Primitive roots
- Discrete logarithm

## Future Work

1. **Automated Testing**: Use hyperpolyglot examples to generate test cases
2. **Cross-validation**: Verify Rust implementations against CAS results
3. **Algorithm Mining**: Extract efficient algorithms from markup files
4. **Documentation**: Generate API docs based on hyperpolyglot syntax

## References

- Hyperpolyglot: https://hyperpolyglot.org/more-computer-algebra
- GAP: https://www.gap-system.org/
- PARI/GP: https://pari.math.u-bordeaux.fr/
- Magma: http://magma.maths.usyd.edu.au/
- Sage: https://www.sagemath.org/

## Tools

- **`src/bin/extract_hyperpolyglot.rs`** - Extracts Monster-relevant concepts
- **`src/bin/parse_computer_algebra.rs`** - Parses markup files

Run extraction:
```bash
cargo run --bin extract_hyperpolyglot
```
