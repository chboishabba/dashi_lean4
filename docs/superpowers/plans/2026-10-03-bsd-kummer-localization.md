# BSD Kummer/Localization Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Close the finite-level explicit-2-descent to genuine cohomological `Sha[2]` bridge on the literal elliptic curve objects already present.

**Architecture:** First discharge geometric `[2]`-surjectivity on `E(Kbar)` using the strongest available Mathlib elliptic/scheme theorem. Then upgrade the already-proved group exactness to continuous Galois-module exactness, construct the Kummer connecting morphism, prove localization naturality, and use the existing square-class/Stoll comparison to identify the explicit cokernel with genuine `Sha[2]`.

**Tech Stack:** Lean 4, Mathlib elliptic curves, algebraic geometry, continuous cohomology.

**Spec:** `docs/superpowers/specs/2026-10-03-bsd-kummer-localization-design.md`

## Global Constraints
- Stay on the literal `GeometricPoint W`, actual `E[2]` subgroup and existing `TopRep` objects.
- Prefer the general nonzero `[n]`-surjectivity theorem over an `n=2` special case when the current API supports it.
- Never assume divisibility, Kummer exactness, localization compatibility, or `C₂(E) ≃ Sha(E)[2]` through record fields.

## Review Focus
- Characteristic assumptions for multiplication-by-`n`/isogeny theorems.
- Algebraically closed field instance must be the same field used by `GeometricPoint W`.
- Surjectivity on scheme points versus surjectivity of a morphism must not be conflated.
- Continuous-action exact sequence must use equivariant maps, not merely underlying group homomorphisms.
- Global/local maps must commute on the same coefficient object before quotienting by Kummer images.

---

### Task 1: Geometric divisibility / doubling surjectivity

**Files:**
- Create or extend: `BSDCohomology/EllipticKummerGeometricDivisibilityExact.lean`

**Interfaces:**
- Consumes: `geometricDoubling`, `EllipticKummerDivisibilityReduction`.
- Produces: preferably `DivisibleBy (GeometricPoint W) ℕ` under algebraic-closed/elliptic hypotheses; minimally `Function.Surjective (geometricDoubling W)`.

- [ ] Search Mathlib for multiplication/isogeny/division-polynomial results sufficient to prove nonzero `[n]` surjective on algebraically closed points.
- [ ] Write the target theorem and a focused example that fails before the proof.
- [ ] Implement the strongest sound route available without assuming surjectivity itself.
- [ ] Kernel-check and commit.

### Task 2: Equivariant short exact Kummer sequence

**Files:**
- Create: `BSDCohomology/EllipticKummerTopRepExact.lean`

**Interfaces:**
- Consumes: Task 1 surjectivity; existing elliptic-point and E[2] TopRep actions.
- Produces: equivariant inclusion/doubling maps and exactness/surjectivity on the actual continuous Galois objects.

- [ ] Prove doubling commutes with the Galois action.
- [ ] Package inclusion and doubling as the repository's actual continuous equivariant morphisms.
- [ ] Prove kernel/image exactness and surjectivity at that level.
- [ ] Kernel-check and commit.

### Task 3: Continuous Kummer connecting morphism

**Files:**
- Create: `BSDCohomology/EllipticKummerConnectingExact.lean`

**Interfaces:**
- Consumes: Task 2 short exact sequence; Mathlib continuous-cohomology connecting-map API if available.
- Produces: global Kummer map from rational points modulo doubling to `H¹(K,E[2])`, with kernel/image theorem.

- [ ] Identify an existing low-degree long-exact/connecting-map API before defining cocycles manually.
- [ ] Instantiate it on the literal elliptic sequence or, if absent, build the minimal degree-zero/one cocycle construction with well-defined quotient proof.
- [ ] Prove exactness at the rational-point quotient.
- [ ] Kernel-check and commit.

### Task 4: Localization naturality

**Files:**
- Create: `BSDCohomology/EllipticKummerLocalizationNaturalityExact.lean`

**Interfaces:**
- Consumes: Task 3 global/local Kummer maps; existing rational-place localization maps.
- Produces: commuting square `loc_v (δ_K P) = δ_Kv (loc_v P)` for every rational place.

- [ ] Instantiate the local Kummer construction on each completion.
- [ ] Prove naturality from functoriality of the connecting morphism or directly on cocycles.
- [ ] Kernel-check and commit.

### Task 5: Explicit Selmer to genuine `Sha[2]`

**Files:**
- Create: `Synthesis/MillenniumBSDExplicitSelmerShaTwoExact.lean`
- Modify: `Synthesis.lean`
- Modify: `.github/workflows/bsd-cohomological-sha.yml`

**Interfaces:**
- Consumes: Task 4 naturality; existing square-class/Stoll descent comparison; actual `cmActualE2ShaTwo` target.
- Produces: explicit/cohomological Selmer equivalence and `ExplicitTwoSelmerCokernel ≃ cmActualE2ShaTwo`; removes the active comparison boundary as a hypothesis.

- [ ] Prove the existing `H¹ ↔ square-class` equivalence transports each local Kummer condition exactly.
- [ ] Build the Selmer equivalence on the same curve.
- [ ] Quotient by the rational Kummer image and prove the cokernel equivalence with genuine `Sha[2]`.
- [ ] Wire focused workflow checks and commit.
