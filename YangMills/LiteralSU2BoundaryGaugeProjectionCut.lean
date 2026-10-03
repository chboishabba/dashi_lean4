import Mathlib
import YangMills.LiteralSU2LinkSectorHaarSplit
import YangMills.LiteralSU2WilsonOSFactorization

/-!
# Exact surviving finite-Wilson boundary gauge-projection leaf

After the literal Haar law is split into positive interior / temporal boundary /
negative interior variables, reflection identifies the negative interior with a
second positive-interior copy, with inversion only on temporal coordinates.

The remaining pure-Wilson object is therefore the boundary-averaged kernel

  K_eff(P,Q) = ∫ db W_full(P,b,Theta Q).

This is not a generic callback: `W_full`, the sector assembly, the selected
reflection convention, and the literal Haar measures are all the same objects
used elsewhere in the finite SU(2) lane.

The previous fixed-boundary counterexample explains why positivity must be
proved only after this boundary Haar average.
-/

namespace RequestProject.YangMills

/-- Reflect a positive-interior link field into the negative-interior sector. -/
def su2PositiveFieldReflectedToNegative
    (n : ℕ) [NeZero n]
    (positive : SU2PositiveInteriorLinks n) :
    SU2NegativeInteriorLinks n :=
  fun q =>
    let p := (su2PositiveNegativeLinkReflectionEquiv n).symm q
    if q.1.2 = su2TimeDirection then
      (positive p)⁻¹
    else
      positive p

/-- The positive-to-negative reflection is measurable. -/
theorem su2_positive_field_reflected_to_negative_measurable
    (n : ℕ) [NeZero n] :
    Measurable (su2PositiveFieldReflectedToNegative n) := by
  apply measurable_pi_lambda
  intro q
  unfold su2PositiveFieldReflectedToNegative
  dsimp
  split <;> fun_prop

/-- Assemble two positive copies and a shared boundary into one literal full link field. -/
def su2AssembleReflectedPair
    (n : ℕ) [NeZero n]
    (left : SU2PositiveInteriorLinks n)
    (boundary : SU2BoundaryTemporalLinks n)
    (right : SU2PositiveInteriorLinks n) :
    SU2TorusLinks (2 * n) :=
  fourDimensionalUnflattenLinks
    (su2LiteralSectorAssemble n
      (left, boundary, su2PositiveFieldReflectedToNegative n right))

/-- Exact full finite Wilson density evaluated on the reflected-pair assembly. -/
def literalSU2ReflectedPairWilsonDensity
    (n : ℕ) [NeZero n]
    (β : ℝ)
    (left : SU2PositiveInteriorLinks n)
    (boundary : SU2BoundaryTemporalLinks n)
    (right : SU2PositiveInteriorLinks n) : ℝ :=
  su2LiteralWilsonProduct
    (su2FourDimensionalPlaquettes (2 * n))
    (su2AssembleReflectedPair n left boundary right)
    β

/--
Boundary-Haar averaged effective Wilson kernel on two positive-interior copies.
This is the exact transfer/gauge-projection object whose positivity closes the
last nontrivial measure-theoretic step of finite Wilson OS2.
-/
noncomputable def literalSU2BoundaryGaugeProjectedWilsonKernel
    (n : ℕ) [NeZero n]
    (β : ℝ)
    (left right : SU2PositiveInteriorLinks n) : ℝ :=
  ∫ boundary : SU2BoundaryTemporalLinks n,
    literalSU2ReflectedPairWilsonDensity n β left boundary right
    ∂(literalSU2BoundaryTemporalHaar n)

/-- Exact, non-vacuous surviving Block-A proposition. -/
def LiteralSU2BoundaryGaugeProjectionRP : Prop :=
  ∀ (n : ℕ) (_ : NeZero n) (β : ℝ), 0 ≤ β →
    ∀ f : SU2PositiveInteriorLinks n → ℝ,
      Measurable f →
      MeasureTheory.Integrable f (literalSU2PositiveInteriorHaar n) →
      0 ≤ ∫ left : SU2PositiveInteriorLinks n,
        ∫ right : SU2PositiveInteriorLinks n,
          f left *
            literalSU2BoundaryGaugeProjectedWilsonKernel n β left right *
            f right
          ∂(literalSU2PositiveInteriorHaar n)
        ∂(literalSU2PositiveInteriorHaar n)

end RequestProject.YangMills
