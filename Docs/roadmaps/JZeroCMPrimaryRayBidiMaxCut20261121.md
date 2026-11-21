# j=0 CM primary ↔ ray normalization — source-first max-cut (2026-11-21)

## Controlling priority
**GRH P0 first**: original pinned Alpöge/Claude fork `UpperTheory.EveryCharacter`, exact all-Dirichlet-character / five published theorem sources, Lean 4.33.1 kernel/axiom and trusted DASHI root/Agda proof admission. This #73 CM lane is a **source-reuse research donor**, not a proof of GRH.

## Recovered ORIGINAL #73 algebraic theorem

`Integration/EisensteinJZeroPrimaryNormalizationExact.lean` owns:
- `IsJZeroPrimary z := Even z.im ∧ jZeroTrace z ≡ 2 [ZMOD 3]`;
- `splitPrime_primary_associate_existsUnique`: for **every** rational split prime p and **every** `z : EisensteinQA` of norm p, there exists exactly one of the six original Eisenstein units u with `IsJZeroPrimary (u*z)`;
- genuine original `splitPrime_primary_unit_unique`, using norm-p, actual unit classification, and a trivial primary stabilizer.

This original #73 theorem is a shorter **universal** donor than the 148 finite Jacobi tests. It does not identify the unit for the specific canonical Jacobi `J_p`, and was not newly kernel checked in this cut.

## New #73 actual proof candidate

`Integration/EisensteinJZeroPrimaryRayModulusBidiExact.lean` imports that original theorem rather than repeating its six-unit orbit. For `f=2+4ω=2√(-3)`, `N(f)=12`, it source-writes:
- `primary_of_ray` : `z≡1 mod f → IsJZeroPrimary z` (no norm premise);
- `ray_of_primary_odd_real` : primary + odd real coordinate → ray-one, with explicit quotient `(v-k)+(k-u)ω`;
- `original_primary_real_odd`: the odd real coordinate follows from the existing norm-p split-prime argument;
- `primary_iff_ray_of_split_norm` : `IsJZeroPrimary z ↔ OneModRay z` on **original norm-p** EisensteinQA;
- `splitPrime_ray_unit_existsUnique`: transport source #73 `∃!u` to **all** split p, **all** norm-p elements, uniqueness of u with `u*z≡1 mod f`;
- `neg_is_ray_of_trace_mod_six` and `neg_one_is_unique_ray_unit_of_trace_mod_six`: if the original element has `Tr(z)%6=4`, specifically `u=-1` is the unique ray normalization.

**Source typecheck/kernel OPEN.** The new statements are source-written candidates; no Lean executable or CI was run.

## Stronger original Frobenius gate instead of new Jacobi orthogonality

For original #69 `E:y²=x³+1`, the convention is `a_p=-Tr(J_p)`. At every good **split** p≡1 (mod3), to identify the uniquely ray-normalizing original unit as -1 it suffices to prove
`a_p≡2 mod6` (equivalently `Tr(J_p)≡4 mod6`).
Rational points `(-1,0)` (order 2) and `(0,1)` (order 3) motivate the universal `6 | #E(F_p)` theorem. This torsion/cardinality result is a **mathematical proof obligation**, NOT already a `#73` source witness or an imported group-theory fact. Given `#E(F_p)≡0 mod6`, the original source `a_p=p+1-#E(F_p)` and `p≡1 mod6` yield `a_p≡2 mod6`.

**Independent exact execution** of curve point counts for **301/301 rational primes 3<p<2000** confirms `#E(F_p)≡0 mod6`; **148/148** split primes have `a_p≡2 mod6`. Independently enumerate **all twelve norm-p elements at each of 148 split primes** (1,776 actual original EisensteinQA coordinate elements): **1,776/1,776** primary iff ray congruence and exactly one of six ray-normalizing units. The user can reproduce from committed `scripts/check_jzero_primary_ray_bidi_trace_mod6_20261121.py`. These are finite exact computations, not Lean proof.

## Cross-branch and global dependencies
- #73 contains original **universal primary associate** source but **does not contain** the latest #69 `splitJacobiEisensteinElement`; #69 has canonical finite character, Jacobi element, full p>3 local Euler family and `RayCongruenceCoordinateCompiler`, but **not** #73's old primary source. **Do not assert they are merged.**
- Next safest integration: choose a branch/PR with real imported source closure, instantiate the #73 primary/ray theorem at the #69 original `splitJacobiEisensteinElement`, and prove `a_p≡2 mod6` on original finite-field point count via genuine 2/3 torsion/cardinality action. No second synthetic character carrier.
- All-prime congruence of original `J_p` by -1 is not yet kernel paid; uniform existence/uniqueness of **some** unit has a pre-existing #73 original proof.
- Global prime ideal assignment/ideal-multiplicativity, exact conductor and infinity type, bad primes 2,3, analytic Hecke Euler product and L(E,s)=L_K(Ψ,s) still OPEN.
- The universal `UpperTheory.EveryCharacter` P0 proof remains a separate, higher-priority admission track.
