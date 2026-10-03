# Hodge Ruling-Swap Design

## Goal
Complete the first end-to-end genuine correspondence regression on PR #40 using the actual relative self-product, factor-swap isomorphism, and `AlgebraicCycle.map` action already present.

## Current paid structure
- Genuine Mathlib `AlgebraicCycle` carrier.
- Genuine pushforward along quasicompact scheme morphisms.
- Relative self-product `X ×[S] X` as a pullback.
- Actual factor-swap isomorphism `pullbackSymmetry f f` exchanging the two projections.

## Immediate closure
Instantiate the construction for `P¹_ℚ`. Choose an explicit rational point section `p : Spec ℚ ⟶ P¹_ℚ`. Construct the two ruling embeddings `i₁(x)=(x,p)` and `i₂(x)=(p,x)` into the exact relative product. Define ruling cycles by pushforward of the fundamental cycle and prove `σ ≫ i₁ = i₂`, `σ ≫ i₂ = i₁`, then `σ_* D₁ = D₂`, `σ_* D₂ = D₁`, and `σ_*(D₁-D₂)=-(D₁-D₂)`.

Use existing categorical pullback/product APIs and actual cycle pushforward; do not assert these identities on the older synthetic rank-two lattice.

## Next seam
Identify the available cohomology/cycle-class API and prove cycle-class compatibility for this same correspondence. Only after that move to genuinely difficult primitive Hodge geometry.
