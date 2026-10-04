# Hodge Ruling-Swap Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Construct actual `P¹_ℚ` ruling cycles in the relative self-product and prove the genuine factor-swap `(-1)` eigendirection on `D₁-D₂`.

**Architecture:** Reuse Mathlib Proj/pullback APIs and the existing `relativeSelfProductSwapCycleAction`. Build the two section embeddings from an explicit rational point, define ruling cycles by actual cycle pushforward, then derive swap identities from morphism equalities and pushforward functoriality.

**Tech Stack:** Lean 4, Mathlib algebraic geometry, `AlgebraicCycle`.

**Spec:** `docs/superpowers/specs/2026-10-03-hodge-ruling-swap-design.md`

## Global Constraints
- Use actual schemes, pullbacks and algebraic cycles; do not promote the synthetic ruling lattice.
- Preserve multiplicities through Mathlib's cycle pushforward.
- Do not claim cycle-class compatibility until a real cohomology/cycle-class API is identified.

## Review Focus
- Relative product must be over `Spec ℚ`, not an absolute categorical product by accident.
- The chosen rational point must define an actual section of the structure morphism.
- Ruling embeddings must land in the exact pullback object used by the swap owner.
- Pushforward functoriality must account for weight/residue-degree conventions.
- `D₁-D₂` proof must use actual additive cycle identities, not synthetic coordinates.

---

### Task 1: Actual `P¹_ℚ` and rational point section

**Files:**
- Create: `Synthesis/MillenniumHodgeP1OverQExact.lean`

**Interfaces:**
- Produces: concrete `P1Q : Scheme`, structure morphism `p1QToSpecQ`, rational point section `pQ : Spec ℚ ⟶ P1Q`, and section law.

- [ ] Identify the current Mathlib Proj/projective-space constructor and write compile-time examples for `P¹` over `ℚ`.
- [ ] Kernel-check the minimal construction.
- [ ] Add explicit rational point/section and prove its structure-morphism law.
- [ ] Kernel-check and commit.

### Task 2: Ruling embeddings into the relative self-product

**Files:**
- Create: `Synthesis/MillenniumHodgeP1xP1RulingEmbeddingsExact.lean`

**Interfaces:**
- Consumes: Task 1 section; `relativeSelfProductSwap`.
- Produces: `i₁ i₂ : P1Q ⟶ pullback p1QToSpecQ p1QToSpecQ`; projection equations; `swap ≫ i₁ = i₂` and `swap ≫ i₂ = i₁` in the correct categorical orientation.

- [ ] Define embeddings by `pullback.lift` and prove both projection equations.
- [ ] Prove factor-swap exchanges them by pullback hom-extensionality.
- [ ] Kernel-check and commit.

### Task 3: Actual ruling cycles and swap eigendirection

**Files:**
- Create: `Synthesis/MillenniumHodgeP1xP1RulingCycleSwapExact.lean`
- Modify: `Synthesis.lean`
- Modify: `.github/workflows/hodge-real-algebraic-cycle.yml`

**Interfaces:**
- Consumes: Task 2 embeddings; `actualCyclePushforward`; pushforward composition theorem or a proved local composition lemma.
- Produces: actual cycles `D₁`, `D₂`; `swap_* D₁ = D₂`; `swap_* D₂ = D₁`; `swap_*(D₁-D₂)=-(D₁-D₂)`.

- [ ] Establish the required `AlgebraicCycle.map` composition/functoriality lemma under the exact weight convention used in the existing action.
- [ ] Define fundamental/ruling cycles on actual scheme points/codimension-one support with no synthetic stand-in.
- [ ] Prove the two swap identities.
- [ ] Prove the difference-cycle `(-1)` eigenidentity by additivity.
- [ ] Wire focused kernel checks and commit.

### Task 4: Cohomology API reconnaissance

**Files:**
- Create a source note/boundary owner only if an actual Mathlib cycle-class/cohomology carrier exists.

- [ ] Search current Mathlib for the relevant scheme cohomology and cycle-class map.
- [ ] If present, state the exact compatibility theorem needed for this same `P¹×P¹` object; otherwise record the missing library primitive without synthetic replacement.
- [ ] Commit only theorem-bearing or exact-boundary source.
