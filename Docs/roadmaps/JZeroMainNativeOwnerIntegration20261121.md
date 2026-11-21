# j=0 Eisenstein / GRH P0 — native main-source integration roadmap

**Date:** 2026-11-21  
**Owner:** `chboishabba/dashi_lean4` `main` native source; integration branch `integration/jzero-jacobi-primary-main-weld-20261121`  
**Priority:** universal **GRH P0** original pinned `UpperTheory.EveryCharacter` kernel/admission remains first; this j=0 CM/Hecke is a special-case donor, never a replacement for every Dirichlet character.

## Exact main audit — do not duplicate merged original owners

All following were fetched **on ref `main`** and checked blob-SHA identical to the corresponding older #69 / #73 source branches:

| Original main path | Source lineage | Main blob SHA | Status |
|---|---|---|---|
| `Integration/EisensteinJZeroPrimaryNormalizationExact.lean` | #73 | `c89010ffbec08bd69d76675dad51cf94b1be30f4` | present |
| `Integration/EisensteinJZeroSplitPrimeEisensteinCarrierExact.lean` | #69 | `e7f9ca9ca58127f51fcc4f9f3d17805129816390` | present |
| `Integration/EisensteinJZeroAllGoodPrimeLocalExact.lean` | #69 | `be61019b6a14f69906c7e9a248872ba93db828d3` | present |
| `Integration/EisensteinJZeroSplitPrimeUnitNormalizationExact.lean` | #69 | `f2db9cd400eb6d0ecc4235d7ed6ec7b1ebadc1f3` | present |
| `Integration/EisensteinJZeroPointCMExact.lean` | #73 | `e0dabf8e63fdab3d09923fef516b8b3bec166f9b` | present |
| `Integration/EisensteinSixUnitOrbitExact.lean` | shared | `4101e424044f46f6c2e4fcabcbc4e72c84aec09c` | present |

Main also has the original cubic Jacobi, finite-field, quadratic-algebra, inert Euler and other prerequisites. **Main does NOT yet have** our newer topic-branch `EisensteinJZeroPrimaryRayModulusBidiExact.lean` (#73), `EisensteinJZeroRayModulusLocalCandidateExact.lean` (#69), `EisensteinJZeroRayCongruenceCoordinateCompilerExact.lean` (#69), `EisensteinJZeroSplitPrimeConjugateEulerFactorExact.lean` (#69).

This is the integration failure: recent additions on stale branches are mistaken for source owners absent from the canonical main repository. Main is thousands of commits ahead of each older branch. As observed from GitHub compare at this point, #69 was 10 ahead / 2191 behind main, #73 was 4 ahead / 2251 behind main; do **not** merge stale topic branch wholesale.

## Main-native theorem composition and the small ported NEW ray BIDI (no copied original owners)

New `Integration/EisensteinJZeroMainJacobiPrimaryWeldExact.lean` consumes **two original main owner modules**, plus only the newer, distinct `EisensteinJZeroPrimaryRayModulusBidiExact` (ported byte-identically from #73 onto this main-based branch):

1. #69 `splitJacobiEisensteinElement p (by omega) hmod : EisensteinQA` with actual `splitJacobiEisensteinElement_norm` and `splitPrime_jZero_trace_formula`.
2. #73 `splitPrime_primary_associate_existsUnique` over original `IsJZeroPrimary z := Even z.im ∧ jZeroTrace z ≡ 2 [ZMOD 3]`, with actual six `eisensteinUnits`.

It source-writes:
- `originalJacobi_norm`: exact source `Norm(J_p)=p`;
- `originalJacobi_primary_unit_existsUnique`: **unconditional**, all split rational primes `p>3`, unique original Eisenstein unit carrying THE SOURCE CANONICAL JACOBI ELEMENT to original primary form (no prior cross-branch merge needed);
- `originalJacobi_trace_eq_negative_frobenius`: SAME source `a_p=-Tr(J_p)`;
- `originalJacobi_ray_unit_existsUnique`: **unconditional** all-split-prime existence and uniqueness of a six-unit normalizer with `OneModRay (u * originalJacobi)`; it composes the ORIGINAL main sources with only the new ray BIDI adapter;
- `OriginalSplitTraceModSixTarget`: the genuine all-split-prime finite-field Frobenius congruence `a_p%6=2`, not a new abstract character;
- `jacobi_trace_mod_six_of_original_source`: conditional arithmetic `a_p%6=2 ⇒ Tr(J_p)%6=4`;
- `originalJacobi_negative_ray_one_if_source_trace` and `originalJacobi_only_negative_one_if_source_trace`: if the SAME original curve supplies `a_p≡2 mod6`, its exact canonical Jacobi is uniquely normalized by the specific unit `-1`.

The source-written composition is a real **proof-candidate theorem application** of the original main declarations and the **new ported ray BIDI**. It does NOT claim new mathematical input proving GRH, an *unconditional* selected unit `-1`, the all-primes trace-mod-six premise, or a global ideal character. The newer BIDI module states ray congruence directly in original `EisensteinQA` using the original #73 primary predicate; no duplicate original six-unit theorem is present. Lean kernel and `#print axioms` execution still OPEN; `lean` / `lake` binaries were absent from the execution container; no CI.

## P1 next acceptance order (main-first)

1. **Build main-source closure**: in compatible pinned Lean environment, first `lake env lean Integration/EisensteinJZeroPrimaryRayModulusBidiExact.lean`, then `lake env lean Integration/EisensteinJZeroMainJacobiPrimaryWeldExact.lean`; inspect `#print axioms`. All three added files in this PR are on the same main-derived branch. The repo `lean-toolchain` declares `v4.35.0-rc3`, `lakefile.toml` requests mathlib `v4.28.0`: inspect the effective resolved Lake manifest/toolchain; do not assume they work together.
2. **Kernel-check the now-ported ray BIDI** `EisensteinJZeroPrimaryRayModulusBidiExact.lean` on this same main-derived branch: `IsJZeroPrimary z ↔ z≡1 (mod 2√(-3))` on original norm-p `EisensteinQA`. The new integrator already reuses this module to assert the **source-written unconditional unique ray unit** for the original `J_p`. Do not duplicate original #73 six-unit proof.
3. **Prove finite-field same-curve point-count/torsion lemma**: for all p>3, rational ((-1,0)) order 2 and ((0,1)) order 3 on `y²=x³+1` imply `6 | #E(F_p)`, so for split `p≡1 (mod6)`, `a_p≡2 (mod6)`; with #69 `a_p=-Tr(J_p)`, this selects the unique primary ray unit exactly `-1`. Existing exact finite tests 301/301 primes and 1776 norm-shell checks are only regressions.
4. **Global Hecke** still needs ideals (not just rational primes), generator/ideal multiplicativity, conductor/infinity type, p=2 and p=3 local factors, analytic Euler product and original `L(E,s)=L_K(Ψ,s)` equality.
5. **Universal GRH P0 remains independent and first**: pinned 4.33.1 fork original `EveryCharacter` theorem, all 5 published statements, same-theorem Lean root admission, kernel/axiom and cross-kernel/Agda semantic transport. A selected CM Hecke example does not prove all-character GRH.

## Reuse discipline

- If source is on `main`, import and apply it; do **not** copy #69/#73 files, or infer a missing proof from a stale topic-branch grep.
- Bring only NEW source-written modules forward in small, reviewable, main-derived commits.
- Treat source-written `#print axioms` lines as pending tests until an actual toolchain runs them.
- Update this roadmap and controlling RH/GRH roadmap with exact branch/ref SHA and PASS vs OPEN whenever a gate changes. Do not overwrite concurrent H07 indexed-cube work.


## 2026-11-21 latest execution policy — defer kernel; SymPy primary local acceptance

**User-directed policy:** defer Lean/Agda kernel acceptance. Do not run CI, do not block iteration on old toolchain/Mathlib version mismatch. Use reproducible exact SymPy algebra + finite-field regression as the working acceptance gate. **Do not call finite tests a universal mathematical proof or a kernel proof**, and do not mark `OriginalSplitTraceModSixTarget` inhabited in Lean merely from finite acceptance. Original GRH P0 source remains first priority, with its formal proof/kernel admission explicitly **DEFERRED** rather than marked completed or impossible.

**Independent local execution** of exact script `/mnt/data/check_main_jzero_sympy_20261121.py` using SymPy 1.14.0:
- PASS symbolic Eisenstein norm-multiplicativity and explicit ray-quotient coordinate identity, exact integer/polynomial algebra;
- PASS 301/301 rational primes (3<p<2000): elliptic group addition on the original SAME curve `E:y²=x³+1`; (P=(0,1)) has (2P=-P,3P=O), (Q=(-1,0)) has (2Q=O); all six combinations of P and Q distinct and (6\mid\#E(\mathbf F_p)) by exhaustive finite point count;
- PASS 148/148 split rational primes in that range: `a_p ≡ 2 mod 6`; original chosen cubic/quadratic Jacobi (J_p) has `N(J_p)=p`, `a_p=-Tr(J_p)`, unique ray-one normalizer precisely `-1`, and `-J_p` is both primary and `1 mod (2+4ω)`;
- PASS all 1,776 norm-p Eisenstein elements on these split shells, primary predicate ↔ exact ray congruence and precisely one ray-one six-unit multiplier.
- Committed standalone corresponding SymPy regression in **THIS main-derived PR**, `scripts/check_jzero_main_native_sympy_acceptance_20261121.py`; its content is constructed from the locally executed mathematical checks, but the exact GitHub file bytes were **not rerun in the local runtime**. Do not misreport a byte-identical replay.

**Universal mathematical observation independent of finite tests:** for any field of characteristic other than 2,3, the curve points P=(0,1), Q=(-1,0) are visibly defined; tangent at P is horizontal, so 2P=-P and 3P=O; y=0 at Q gives 2Q=O. In the elliptic group, 2- and 3-order rational points produce a subgroup of order 6. To promote this into the repository's **original same-field finite-field point-count theorem**, a source-written exact group/cardinality adapter remains OPEN. SymPy finite acceptance supports—but does not instantiate—the Lean all-primes theorem. It is reasonable to pursue the next Hecke ideal-conductor / multiplicativity cut while kernel acceptance remains deferred.

**PR acceptance labels now:** original #69/#73 source ownership/real main import = confirmed by GitHub blobs; symbolic algebra and finite regression = PASS; universal actual `OriginalSplitTraceModSixTarget` Lean proof = OPEN/deferred; all-prime unique primary↔ray Lean source-written candidate = not kernel accepted/deferred; global ideal Ψ, conductor/infinity type, all bad-prime factors, Euler/L-series = OPEN; original pinned all-character GRH P0 source/kernel admission = DEFERRED per user, not mathematically closed.


## 21 November — latest exact ray CRT / normalized PRINCIPAL-IDEAL Hecke-shape cut

**Execution policy unchanged:** SymPy exact arithmetic and finite-field checks are operational acceptance; Lean/Agda kernel, axioms, toolchain and CI are **DEFERRED** by user direction, not reported as proof.

Original source owners still reside on `dashi_lean4@main` (#69 Jacobi, #73 primary normalization, Eisenstein Euclidean/PID machinery), with new code on main-derived [draft PR #114](https://github.com/chboishabba/dashi_lean4/pull/114). No original source is copied.

**New FULL FINITE RAY QUOTIENT acceptance (not merely 148 prime samples):**
- The literal Eisenstein modulus `f=2+4ω`, norm 12, induces explicit CRT residue key `(a mod2,b mod2,(a+b) mod3)`. The quotient `O_K/(f) ≅ F₄ × F₃` has **12/12** classes; `F₄` comes from `ω²+ω+1` irreducible mod2, `F₃` from the ramified `ω↦1` at `√−3`.
- All **144 ordered quotient-pair multiplications** agree under changed integral representatives. Exactly **6 quotient units**, exactly the six distinct original `μ₆` residue classes. For any integral Eisenstein z with `gcd(N(z),6)=1`, the CRT residue is a unit and there exists a **unique** `u∈μ₆` with `u*z≡1 (mod f)`. The finite quotient classification supports this claim for arbitrary coprime z; this is not derived by extrapolating bounded prime tests.
- Source-local reproducible script `scripts/check_jzero_hecke_ray_quotient_sympy_20261121.py`. Independently executed equivalent exact local Python/SymPy 1.14.0: 304/304 bounded elements `a,b∈[-12,12]`, exact quotient-integrality and six-unit normalizations; **23,104/23,104 ordered generator pairs** obey `normalize(z*w)=normalize(z)*normalize(w)`; full six-unit associate invariance; original 148/148 split Jacobi values still normalized by exactly `−1`.
- This builds a canonical **multiplicative normalized generator of coprime principal ideals**: since all integral ideals in Euclidean `Z[ω]` are principal, one can mathematically extend to integral ideals prime to f by uniqueness of the unit. However: the actual original Lean same-ideal quotient/class identity, domain and global `Ψ : ideals → K` plus fractional ideals **have not been instantiated or kernel-checked**. Do not confuse exact arithmetic quotient with full formalized Hecke Grössencharacter or analytic L-series.

**New SAME-CHARACTER local factor check:** `scripts/check_jzero_hecke_local_ideal_factors_sympy_20261121.py` consumes exactly the same normalization function as the CRT test. In equivalent locally executed exact Python: all **148/148 split p** have conjugate norm-p normalized generators `α=-J_p`, `ᾱ`, with `(1−α T)(1−ᾱ T)=1−a_pT+pT²`. All **153/153 inert p** have the unique normalized generator `normalize(p)=-p` for the degree-two ideal `(p)`; its Hecke-shaped factor `1−Ψ((p))T²=1+pT²` matches same curve's inert factor. **301/301 good rational primes 3<p<2000** agree. This is genuinely the same candidate ray normalization on BOTH split and inert branches, not two unrelated ad hoc local formulae.
- At finite quotient/element level, multiplicativity is confirmed. The ideal-level statement additionally depends on actual integrality/ideal equality and prime-ideal selection; for `Z[ω]` known Euclidean source this is mathematically accessible, but **analytic Euler-product identity, convergence/continuation, exact Hecke conductor and infinity type, ramified/bad p=2,3 factors and all-character GRH remain open**.
- The committed GitHub Python files encode the same exact computations; **they were not byte-for-byte rerun after remote commit**. The local equivalents were run and passed. Keep these two receipts distinct.

**NEXT maximal cut:** source-own the actual ray-normalized integral ideal generator as a multiplicative map on `Ideal (Z[ω])` prime to `f`, using existing main `EisensteinEuclideanDomainExact` and PID/ideal-class machinery; compute the conductor, infinity-type and the exceptional p2/p3 local factors; then global Hecke L-series as a genuine same-object `Ψ` rather than a matching finite-factor catalogue. Maintain GRH P0 universal `UpperTheory.EveryCharacter` priority with kernel admission deferred.


## 2026-11-21 — NEW highest local CM cut: HNF integral ideals → fractional ray character → conductor obstructions

**Execution policy:** user requested **SymPy, kernel acceptance DEFERRED**. The original #69 Jacobi and #73 six-unit primary modules are BOTH in main. Do not duplicate or create another identity carrier. New scripts below are on the main-derived draft #114.

### A. Actual integral IDEAL multiplication, not just element multiplication

Committed `scripts/check_jzero_hecke_ideal_hnf_sympy_20261121.py`, with independent **executed** SymPy 1.14.0 local equivalent `/mnt/data/check_jzero_ideal_hnf_sympy_20261121.py`:

- `O_K=Z[ω]` identified as lattice `Z²`; principal ideal `(z)` represented by actual integer HNF lattice of span `{z,ωz}`, multiplication matrix `[[a,-b],[b,a-b]]`, determinant `N(z)`.
- Recover a generator **from the HNF itself** using exact nearest-coordinate Eisenstein Euclidean gcd of its two basis columns (the original main `EisensteinEuclideanDomainExact` corresponds to this source algorithm). Verify recovered generator norm = ideal lattice determinant and reconstructed HNF equals original, no arbitrary chosen generating element retained.
- Define candidate integral ideal character `Psi(I)=normalize(gcd(HNF(I) columns))` when `gcd(N(I),6)=1`. Check unit-associate independence; form ideal products using **all four pairwise basis-vector products**, take their lattice HNF and verify `Psi(IJ)=Psi(I)Psi(J)`.
- Exact local acceptance: symbolic norm multiplicativity PASS; **80** coprime coordinate elements across **20** distinct integral ideals, all generator/HNF character checks PASS; **400/400** ideal HNF products, norm determinant equality and character multiplicativity PASS; **384** associate-choice negative controls PASS.
- This is a true integral ideal lattice model; the mathematical all-integral-ideal extension follows from Eisenstein PID + six-unit quotient, but **actual Lean `Ideal` proof/character source remains uncompiled and kernel deferred**. No analytic theorem claimed.

### B. Fractional ideal character as ratio of the above actual integral ideals

Committed `scripts/check_jzero_hecke_fractional_ideal_sympy_20261121.py`. Independent **executed** local equivalent `/mnt/data/check_jzero_fractional_ideal_sympy_20261121.py` uses exact `Fraction` coefficients in `Q(ω)`, with `Psi(A/B)=Psi(A)/Psi(B)` and ratio equality via cross-ideal HNF multiplication `AD=CB`:
- **9** distinct integral ideals in smaller chosen corpus; **81/81** localized ideal fraction equivalence/inverse/identity tests PASS; **441/441** fraction multiplication homomorphism tests PASS.
- **7** source principal-ray evaluations `Psi((z))=z` for `z≡1 mod 2√−3` PASS, explicitly recording the candidate algebraic **infinity type one**.
- Mathematical construction is now explicit on the localization of ideals coprime to conductor, rather than merely a hypothetical map on rational primes. It is **not** an installed Lean type `HeckeCharacter`, not a fully formal proof about all ideals and not an analytic Euler-product/L-series equality.

### C. Ray-conductor necessity / bad model negative controls

Committed `scripts/check_jzero_ray_conductor_sympy_20261121.py`, with independently **executed** local exact equivalent `/mnt/data/check_jzero_ray_conductor_sympy_20261121.py`.
- `f=2(1+2ω)=2√−3`, norm `12`, has trivial six-unit congruence kernel.
- Omitting `2`: `−1≡1 mod (2)` — violates type-one principal-unit rule.
- Omitting `√−3`: `ω≡1 mod (√−3)` — violates the same rule.
- Both factors thus necessary **among divisors of f**; this supports the modulus/conductor minimality of the candidate but is not a separate full Artin/Tate conductor computation.
- Original curve (y²=x³+1) has singular reductions at both `p=2` and `p=3`, confirmed exact Fp derivative/equation enumeration. **DO NOT infer** exceptional Euler factors, Kodaira symbols, additive conductor exponents or analytic level from singularity alone.

### D. Reconciled remaining gates

**CM algebraic:** completed exact finite quotient; constructive integral and fractional ideal-character model with exact SymPy acceptance (bounded tests + general structural derivation). Still need source-typed global domain/infinity-type/ray conductor proof, especially theorem that `Psi` is independent of `A/B` and multiplicative for **arbitrary** coprime fractional ideals, not only tested corpus. **CM analytic:** compute and verify bad p=2,3 local Euler factors via actual Tate/reduction data, derive conductor 36 rigorously, then Euler-product/global analytic equality `L_K(Psi,s)=L(E,s)`. **GRH P0 remains highest logical objective**: original pinned all-character `UpperTheory.EveryCharacter`; formal kernel admission remains DEFERRED by user direction, never marked proved. SymPy cannot verify universal GRH.
