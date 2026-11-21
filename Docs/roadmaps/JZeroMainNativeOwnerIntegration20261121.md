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


## 21 November — WELD-FORWARD exact commuting square/cube in the original conductor ray (NEW)

**Methodology (user explicitly reinforced):** **weld forward** = start from existing strongest source owners **on actual `main`**; search modern merged/active donor proofs before assuming absence; retain source carrier and identities; implement only the smallest missing same-object bridge; test it directly and append to canonical roadmap/PR. When an equality fails, inspect original geometry/normalization/representation before inventing a new object. Use steelman BIDI: start from the solved consumer and trace backward to the earliest genuinely missing producer; distinguish already-owned theorem, equivalent representation, unproved identification and new mathematics. Preserve original #69 Jacobi, #73 six units/primary, Euclidean lattice/HNF, and #114 fractional `Psi`; avoid rebuilding any. **SymPy exact acceptance**, Lean/Agda kernel and CI deferred.

### Commuting C2 sign × C3 cubic factor square

**Original same ring:** (O_K=\mathbf Z[\omega]), (\omega^2+\omega+1=0), (f=2\sqrt{-3}=2+4\omega).
Existing exact CRT quotient (O_K/(f)\simeq\mathbf F_4\times\mathbf F_3) has unit group (\mathbf F_4^\times\times\mathbf F_3^\times\simeq C_3\times C_2\simeq\mu_6).

The **literal commuting-square/cube weld** for an original Eisenstein unit (u\in\mu_6) is
[
 u_2=u^3\in\{\pm1\},\qquad u_3=u^4\in\{1,\omega,\omega^2\},
\qquad u=u_2u_3=u_3u_2.
]
(u_2^2=1), (u_3^3=1), and powers commute: ((u^2)^3=(u^3)^2=u^6=1). In CRT terms (u_2\equiv1\pmod2) (lives entirely in (\mathbf F_3^\times)) and (u_3\equiv1\pmod{\sqrt{-3}}) (lives entirely in (\mathbf F_4^\times)). The residue diagram commutes because (\mu_6\xrightarrow{\sim}(O_K/f)^\times\), projecting to the respective factors and multiplying the canonical inverse residues is equivalent to ray-normalizing at once. **Do not identify** square map with a ring automorphism: powering acts multiplicatively on units, while (F_4\times F_3) is the underlying ring CRT.

**Correct conductor obstruction ordering:** modulus (2) alone retains kernel \(\{1,-1\}\) (cannot separate sign); modulus (\(\sqrt{-3}\)) alone retains kernel \(\{1,\omega,\omega^2\}\) (cannot separate cubic phase); full product modulus has trivial unit kernel. Both conductor prime-power factors essential **among divisors of f** for a type-one principal ray normalization. This is distinct from a Tate/Artin conductor calculation.

**Committed NEW exact test** `scripts/check_jzero_commuting_square_cube_sympy_20261121.py` on main-derived #114; actual byte-matched local Python/SymPy 1.14.0 was executed **before commit**:
- PASS **12/12** quotient elements and all **144/144** multiplicative quotient pairs;
- PASS entire six-unit group (u=u^3u^4=u^4u^3), `C2 x C3` projections and **36/36** ordered pairs' commute/multiplicative power identities;
- PASS both reduced-modulus unit kernel negative controls and full trivial kernel;
- PASS **304/304** coprime coordinate generators (range [-12,12]) under commuting split-normalizer reconstruction.
This is complete for the finite quotient/units, bounded for the 304 nonunit generators, not a Lean kernel or universal GRH proof.

**Same-object next weld (do not start a new character):** consume original #114 `Psi(I)=normalize(gcd(HNF(I)))` and `Psi(A/B)`, compare its unique ray normalizer to independently reconstructed `C2\times C3` component inverses on actual HNF ideals and fractional ideal representatives; then inspect bad-prime (2,3) conductor/local-factor data using existing published owners before new Tate machinery. Kernel/CI remain deferred, and the global analytic (L(E,s)=L_K(\Psi,s)) remains OPEN. Universal all-Dirichlet GRH P0 original `EveryCharacter` remains higher-priority and independent.


### 21 November weld-forward completion — actual HNF IDEAL commuting diagram

The smallest next bridge has now been written as `scripts/check_jzero_commuting_ideal_weld_sympy_20261121.py`, importing the **two existing source-owned scripts**: `check_jzero_hecke_ideal_hnf_sympy_20261121.py` (HNF ideals, Euclidean-generator/Psi owner) and `check_jzero_commuting_square_cube_sympy_20261121.py` (complete CRT/unit (C_2\times C_3) owner). It does NOT introduce another ideal ring, quotient, normalization, character or generator.

**Commuting source diagram:**
[
\begin{array}{ccc}
 I\subset \mathbf Z[\omega] &\xrightarrow{\mathrm{HNF\ gcd}}& z\in\mathbf Z[\omega]\\
 \downarrow\Psi &&\downarrow\bigl(u_2(z),u_3(z)\bigr)\\
 \alpha_I=\mathrm{normalize}(z)&\xleftarrow{\quad(u_2,u_3)\mapsto u_2u_3 z\quad}&
 C_2\times C_3
\end{array}
]
where (u_2=u^3), (u_3=u^4), `u=normalizer(z)`, selected by CRT inverse of the SAME original HNF generator. Multiplication of ideals uses all four basis-vector products, then integer HNF. Unit-associate replacement `z→v z` must not change either end of the diagram.

**Independent locally executed exact SymPy 1.14.0**: 80/80 original HNF generator instances, **480/480** associates, **400/400** HNF-ideal-product/commuting CRT character weld comparisons PASS. Local earlier HNF owner used `generator_from_hnf` / `ideal_character`, while committed GitHub #114 owner uses `ideal_generator` / `psi`; new weld explicitly accepts **either** existing export signature, with unchanged underlying ring/ideals. **Committed new weld file was source-written from the equivalent local test, but remote exact bytes not rerun**. Do not promote this finite acceptance to a universal Lean `HeckeCharacter` proof.

**Forward next mathematical gate:** check actual K/Q local/global Hecke normalization and modular-form/elliptic identification at p2 and p3, using original main sources. Keep full Fp 2/3-torsion and special -Jacobi unit semantics separate from CRT unit factor split; power map (u↦u²) and (u↦u³) is NOT the same thing as conductor primes 2 and 3 or elliptic scalar multiplication [2]/[3]. All these operators coexist but need explicit same-object welds; do not collapse them by identical numerals. Kernel/CI deferred; GRH P0 original `UpperTheory.EveryCharacter` stays logically first.


## 21 November — bad-prime and Euler-coefficient WELD-FORWARD: p=2,3 now sourced

**Strategy:** Original `dashi_lean4@main` has #69 same-curve (E:y^2=x^3+1) good-prime Jacobi/inert Euler owners and #73 primary ray normalization. Keep them untouched. #114 is a main-derived narrow adapter and SymPy execution producer. User explicitly **defers Lean/Agda kernel and CI**, not the mathematical work.

### Exact same-curve exceptional prime reduction

The model (y^2=x^3+1) has discriminant (Delta=-432=-2^4 3^3), so this integral Weierstrass equation is locally minimal at p2/p3 (valuations <12, preventing an integral change lowering discriminant). At p=2 the unique singular point is ((0,1)), and p=3 the singular point is ((2,0)). Translate the singularity: (overline{F}(u,v)=v^2-u^3) over each finite field, **cusp (additive)**. Enumerate the smooth locus of the original reduced projective model (all affine solutions except singular point, plus infinity):
- p=2: **2** smooth Fp-rational points, equal p;
- p=3: **3** smooth Fp-rational points, equal p.

For a minimal additive elliptic curve reduction, `a_p=0`, local inverse Euler polynomial `1`. See external standard classification https://www.mdpi.com/2227-7390/14/4/697 (Definitions 14/15/17) and independent authoritative LMFDB **exact original same curve** https://www.lmfdb.org/EllipticCurve/Q/36/a/ (row **36.a4 / Cremona 36a1**, coefficients [0,0,0,0,1], discriminant -432, CM -3, conductor 36). LMFDB lists **bad L-factors (p2:1, p3:1)**, and good factors p5/7/11/13/17/19 equal original Jacobi/inert results. **Conductor (N_E=36=2²3²) is externally corroborated**, NOT independently derived by local SymPy wild-Tate algorithm. Do not mix the norm12 *Hecke ray modulus* with the integer norm36 *elliptic Artin conductor*; their relationship demands the CM conductor/discriminant formula, separate from source-model singularity.

### Reproducible exact tests (kernel deferred)

- **Actually executed** local `/mnt/data/check_jzero_bad_primes_20261121.py` with SymPy 1.14.0: both translated cusp equations, exact minimal discriminant valuations, singularity point enumeration and smooth point counts, inverse bad Euler polynomial 1: **2/2 PASS**. It also computed the 600-slot same-curve good/bad Dirichlet recurrence with bad-prime zeros, PASS.
- **Actually executed** independent `/mnt/data/check_jzero_hecke_euler_weld_20261121.py`: split prime local value from **canonical cubic/quadratic Jacobi** `Jp` ray-normalized via the same original `−Jp`, inert local ideal `(p)` ray-normalized to `−p`, ramified conductor primes p2/p3 explicitly **omitted**, producing Euler polynomial 1; compare to an **independent elliptic Legendre-character finite-field point count**. **107/107** good primes up to 600 and **600/600** exact rational Dirichlet coefficient slots agree. Bad factors and sample good coefficients match LMFDB 36.a. Test includes actual prime-power recurrences `a(p^k)=a(p)a(p^(k-1))−p a(p^(k-2))`, and zero all n divisible by p2 or p3.
- Committed corresponding files in **main-based PR #114**: `scripts/check_jzero_bad_prime_reduction_sympy_20261121.py` and `scripts/check_jzero_hecke_euler_weld_sympy_20261121.py`. Both committed files implement the same tests; **exact byte-identical post-commit replay not asserted**.

### What is closed versus open

- **CLOSED finite/arithmetical local acceptance:** exact additive cusp and bad polynomial 1 for BOTH bad p2,p3, 107 good primes tested, 600 Dirichlet coefficients independently matched to the same original CM ray prime-ideal assignments. The *definition* of the Hecke Euler product on unramified prime ideals omits those dividing the conductor; no artificial p2/p3 eigenvalues.
- **EXTERNAL lookup confirmed:** same curve LMFDB 36.a4 / conductor 36 = 2²3²; new arithmetic runs do **not** independently pay wild conductor exponents or proof of global character identification.
- **STILL OPEN:** source-typed global Hecke ideal character/Psi well-definedness on *every* coprime fractional ideal (SymPy bounded checks and algebraic construction exist), exact conductor/infinity type to modulus/conductor formula, p2/p3 Tate wild exponents, equality of **analytic functions** `L(E,s)=L_K(Psi,s)`, completed L-functions and GRH P0 all-character result. Kernel/CI **DEFERRED** by user direction, not proof closed.

**Next maximum cut:** use main's original ideal character carrier plus source LMFDB modular form **36.2.a.a** or original modular/L-series source, test deeper finite q-coefficient or modular-form correspondence, preserve exact same-object provenance. Do not posit a new elliptic curve just because 36.a has 4 isogenous curves. GRH P0 original `UpperTheory.EveryCharacter` remains higher priority; kernels deferred.


## 2026-11-21 same-E bad-prime conductor / global Euler WELD FORWARD

**EXACT external data** [LMFDB 36.a4 (Cremona 36a1)](https://www.lmfdb.org/EllipticCurve/Q/36/a/4) identifies original curve literally `[0,0,0,0,1]`, `y²=x³+1`; conductor 36=2²·3², minimal discriminant -432=-2⁴·3³, j=0, CM discriminant -3, torsion Z/6. Its LOCAL reduction table: p=2 additive type IV, ord Δ=4, ord conductor=2, Tamagawa=3; p=3 additive type III, ord Δ=3, ord conductor=2, Tamagawa=2. The LMFDB /data/36.a4 isogeny-class `anlist` gives the first twenty coefficients 1,0,0,0,0,0,-4,0,0,0,0,0,2,0,0,0,0,0,8,0. These external Tate/Kodaira/exponent data are ACCEPTED as source evidence, NOT claimed independently rederived from the local SymPy model.

**New committed source** `scripts/check_jzero_bad_prime_global_euler_20261121.py` imports existing PR #114 `check_jzero_hecke_ray_quotient_sympy_20261121.py` instead of reinventing Jacobi or ray normalization; independently gets good-prime curve trace from quadratic point-character sum; computes bad prime traces by counting ONLY the nonsingular locus of the actual singular reduction and adding infinity; expands elliptic/CM Euler local coefficient recurrences to n≤600.

**Independent exact local SymPy 1.14.0 run** of equivalent `/mnt/data/check_jzero_bad_prime_global_euler_20261121.py` PASSED: p=2 singular (0,1), 1 smooth affine + infinity=2 => bad a₂=0; p=3 singular (2,0), 2 smooth affine + infinity=3 => bad a₃=0. Both additive inverse bad polynomials `P_2(T)=P_3(T)=1`. Negative controls show including singular points produces WRONG a₂=a₃=-1. All **107/107** good rational primes ≤600: independent same-curve point-count trace equals same-ray CM Jacobi/ideal normalized trace. **600/600** exact integer Dirichlet coefficients agree, **400/400** indices divisible by 2 or 3 have zero coefficient, and **20/20** initial coefficients match LMFDB 36.a4 `anlist`. The remote committed file has **not** been byte-identically rerun: no false remote CI/kernel claim.

**Math/proof debt remaining:** This completes finite bad Euler polynomials at the exact original model and finite Euler-product coefficient acceptance, NOT analytic convergence/continuation, an infinite global L-series proof or a full source-typed all-ideal Hecke character. Conductor exponent 2 at 2 and 3 and Kodaira symbols are external LMFDB provenance; a genuine original Tate/wild-conductor derivation remains open, or could be bridged via proven minimal-discriminant and Kodaira/Ogg local-conductor identities with exact hypotheses. GRH P0 original universal EveryCharacter is a distinct higher mathematical target; Lean/Agda kernel and CI DEFERRED per user.


### 21 November — additional rigorous Ogg conductor BIDI: external local Kodaira ⇒ exact wild exponents

Instead of blindly copying the conductor exponent from LMFDB, consume the **original same minimal equation** and LMFDB verified local reduction types via the classical **Ogg–Saito formula** (f_p=v_p(\Delta_{\min})+1-m_p), where (m_p) counts *geometric irreducible components of the minimal regular special fiber*. Authoritative general formula sources: J. Silverman, *Advanced Topics in Arithmetic of Elliptic Curves*, conductor/Ogg overview; [MathWorld Local Conductor Exponent](https://mathworld.wolfram.com/LocalConductorExponent.html). For the EXACT source `E:y²=x³+1`, LMFDB 36.a4 certifies minimum `Δ=-432=-2^4·3^3`, type IV at 2 with `m₂=3`, type III at 3 with `m₃=2`. Hence **exact conditional derivation** `f₂=4+1−3=2`, `f₃=3+1−2=2`, `N=2²·3²=36`. This formula accounts for wild contributions without assuming the tame conductor exponent; it still **depends on externally verified Kodaira types/minimality**, which were not independently computed by Tate's algorithm. Do not promote to self-contained Tate acceptance.

Committed `scripts/check_jzero_conductor_ogg_20261121.py` on #114; independent local file `/mnt/data/check_jzero_conductor_ogg_20261121.py` executed with SymPy 1.14.0 PASS minimal discriminant factorization, Ogg exponents and N=36. Exact committed GitHub file not byte-identically replayed after commit. Prior 600-slot Euler comparison and bad inverse factors 1 remain unchanged. **Next real analytic gate**: global equality of formal Euler products using all-prime local identification (not just n≤600), convergence for Re(s)>3/2, and explicit same ideal-character/elliptic analytic continuations and functional equations. All-character GRH P0 and kernels remain separate/deferred.


### 2026-11-21 final WELD-FORWARD deduplication and ownership correction

**Supersedes the previous note naming a new combined bad-prime/Euler producer**: that overlapping script `scripts/check_jzero_bad_prime_global_euler_20261121.py` was **deleted from PR #114**, after discovering already-present, owner-specific PR #114 scripts `scripts/check_jzero_bad_prime_reduction_sympy_20261121.py` and `scripts/check_jzero_hecke_euler_weld_sympy_20261121.py` (on the very same main-based branch). Do not resurrect the duplicated file or treat its deleted commit as a current implementation.

The existing original Euler producer `check_jzero_hecke_euler_weld_sympy_20261121.py` was then **rewired to import the existing shared `check_jzero_hecke_ray_quotient_sympy_20261121.py`**: `mul/norm/chi/jacobi/normalize` now defer to the original ray/Jacobi owner rather than defining another table of cubic roots, six units, or source character. Its independent elliptic point count and 600-slot coefficient generator are retained. The original bad-reduction producer retains the exact singular/cusp, minimal Δ and smooth locus calculation.

**Only NEW consumer** `scripts/check_jzero_lmfdb_euler_receipt_weld_20261121.py` imports BOTH already-owned producers and checks **600/600** coefficient agreement, **400/400** indices divisible by 2 or 3 zero, first **20/20** stored `LMFDB 36.a4` `anlist` coefficients, and bad smooth-locus vs erroneous all-singular-point counting negative controls; it is a provenance/acceptance cross-check, **not** another curve/Jacobi/character calculation.

Independent exact local equivalent `/mnt/data/check_jzero_bad_prime_global_euler_20261121.py` and the already-mounted original `/mnt/data/check_jzero_bad_primes_20261121.py` + `/mnt/data/check_jzero_hecke_euler_weld_20261121.py` passed 600 coefficients and the original bad smooth locus. The newly committed GitHub audit byte stream has not been separately executed in the local container; mark this source-written combined consumer **kernel deferred / byte-execution pending** rather than claiming identical replay. The separate exact `scripts/check_jzero_conductor_ogg_20261121.py` is retained and non-duplicative: it compiles source LMFDB Kodaira IV/III and minimal Δ into (N=36) via Ogg, with the Tate type source-dependency explicit.

**Canonical forward stack now**: actual `main` #69 Jacobi / #73 primary → PR #114 ray CRT → PR #114 HNF fractional ideal Ψ → **existing** bad reduction and Euler coefficient owners → **NEW** LMFDB receipt consumer and Ogg conduit. Full analytic Euler product/continuation and all-character GRH remain separate OPEN mathematical gates. User-requested SymPy operational acceptance only; Lean/Agda kernels and CI remain DEFERRED.


## 2026-11-21 — infinity-half-plane CM Euler bridge and external RH/Dirichlet-GRH acceptance

**WELD-FORWARD RULE CONTINUES:** consume original source-owned #69 canonical Jacobi, #73 primary and the shared PR #114 CRT/HNF ideal `Psi` and existing bad-prime/Euler coefficient producer. Do NOT invent another Hecke character, parallel Jacobi sum or RH zero predicate. Kernel/CI intentionally deferred per user; SymPy exact symbolic/finite acceptance remains operational, not a substitute for a universally quantified proof.

**REAL regression discovery and fix:** the earlier producer rewrite of `scripts/check_jzero_hecke_euler_weld_sympy_20261121.py` had `chi=_ray.chi`, but the ORIGINAL shared ray script exports `quadratic`, not `chi`. Fixed on #114: `chi=_ray.quadratic`. An independently executed local owner-equivalent pipeline then PASSED all **107/107** good-prime CM/elliptic traces and **600/600** exact Dirichlet-coefficient slots. Do not rely on pre-fix 600-slot receipts for the actual committed import graph.

**NEW minimal analytic bridge:** `scripts/check_jzero_infinite_euler_convergence_weld_sympy_20261121.py` imports the existing Euler producer (which imports the actual shared Jacobi/CRT producer), instead of recreating the local arithmetic. The **conditional mathematical theorem schema** is:

Let `Ψ` be the actual conductor-`f=2√−3`, infinity-type-1 ideal character on the coprime ideals in `K=Q(√−3)`, with source-owned same-prime local factor equalities for **every** rational prime (p), including `P₂=P₃=1`. Given the standard Hasse bound ( |a_p|\le 2\sqrt p ) (or directly (|\alpha_{\mathfrak p}|=\sqrt{N\mathfrak p}\) for split degree-one ideals and (|\Psi((p))|=p) at inert degree-two ideals), for `σ=Re(s)>3/2`, all good-prime local logarithms are absolutely summable. Define (q_p=p^{1/2-\sigma}\); split log absolute value `≤2 q_p/(1-q_p)`, inert log `≤q_p²/(1-q_p²)`; since `p≥5`, `q_p<1/5`, both `≤4 q_p`. Therefore
[
 \sum_{p>P} |\log L_p(s)| \le 4\sum_{p>P}p^{1/2-\sigma}
 \le \frac{4P^{3/2-\sigma}}{\sigma-3/2},\qquad P\ge5,\ \sigma>3/2.
]
Since **identical factors at all primes** imply identical finite partial products, absolute convergence passes equality to the infinite Euler products:
( L(E,s)=L_K(\Psi,s)\) for `Re(s)>3/2`. This deduction does NOT infer all-primes equalities merely from the observed finite tests. Standard analytic continuation plus identity theorem can then extend equality when the precise continuation objects and normalizations are supplied; these are **separate source receipts**. This half-plane does NOT intersect the critical line and cannot prove RH, Dirichlet GRH or zeros of `L(E,s)`.

**New local SymPy 1.14.0 execution:** symbolic norm/conjugate factor identities, proof-majorant derivative nonnegativity, exact integral prime-tail certificates at `σ=2: 8/√P`, `σ=7/4:16/P^(1/4)`, **107/107** original CM-vs-elliptic good-prime traces, **600/600** Dirichlet coefficient equality, and independent exact rational truncated Euler products at `s=2` for cutoffs `31,97,599` PASS. Numeric values about `0.9411137810`, `0.9375029041`, `0.9395920290` respectively. An initial numeric test denominator was corrected to `p³-a_p p+1`; earlier uncorrected numbers must not be cited. Remote committed bytes of the new regression have not been independently replayed; local equivalent code executed.

### Their November 2026 RH/GRH proof: keep three levels strictly separate

**External independent formal checking is NOW STRONG**: [Andrew Sutherland's MIT report](https://math.mit.edu/~drew/grh/) updated **2026-11-20 22:05 UTC** records source build **175,187/175,187** modules, five original `Main` theorem axiom audit `propext,Classical.choice,Quot.sound` only, module-by-module `leanchecker` replay, full exported-proof `nanoda` and `con-leche` independent kernel acceptances, `lean4lean` all-module acceptances, and `con-leche --compare` full 5-theorem source challenge matching. The default/paranoid exported-proof kernel runs and end-to-end `lake comparator` were still running on that timestamp. Additional [LUMI independently verified full 175,187 module build](https://github.com/aapolipponen/rh-lean-check-lumi). This is **substantial external verification**, not merely a claimed untested proof. Its published scope is ORIGINAL ordinary Mathlib RH + all Dirichlet-character nonvanishing / zero-location GRH (five published terminals), **not** all Hecke/motivic GRH. As of the inspected records, we do not assert Clay prize award or universal mathematical community acceptance.

**Our pinned source BIDI**: [Lean #113 `RHGRHP0DirectionalSourceCut.lean`](https://github.com/chboishabba/dashi_lean4/blob/research/alpoge-rh-source-admission-20261121/proofs/alpoge-lean433/RHGRHP0DirectionalSourceCut.lean) consumes `UpperTheory.EveryCharacter` and original `Claim.Zeta ↔ Mathlib.RiemannHypothesis`, as well as `Claim.strip` and `Formalism.VW.critLine`. This is one-way all-Dirichlet `EveryCharacter → RH`; ordinary RH alone does not source-give all-character GRH. **DASHI's own** 4.33.1→root 4.35.0 / Agda semantic and trusted proof import remains DEFERRED, not accepted. Our original Agda independent G2 signed Off/Gamma analytic estimates remain OPEN and are not automatically paid merely by the external theorem.

**CM special Hecke branch DOES NOT upgrade RH/GRH:** even if the global L-series identity is established for (E:y²=x³+1), equality of functions gives **no** location-of-zeros assertion. Alpöge's externally checked Dirichlet-GRH scope does **not** include this infinite-order infinity-type-one CM Hecke (L)-function; automorphic/Hecke GRH would need independent proof. Thus our CM/Euler work is useful same-source arithmetic/analytic infrastructure, not a new proof of their RH/Dirichlet GRH or a corollary establishing elliptic GRH.

**NEXT exact mathematical gate:** source-prove all-prime same-ideal `Ψ(𝔭)` local identifications (not just n≤600), take the conditional half-plane convergence theorem to an honest infinite identity, then attach the analytically continued/functional-equation objects with exact gamma/conductor normalizations. For external RH/Dirichlet GRH, P0 remains the pinned `EveryCharacter` source and its *locally deferred* cross-version/Agda proof transport, not this CM lane.
