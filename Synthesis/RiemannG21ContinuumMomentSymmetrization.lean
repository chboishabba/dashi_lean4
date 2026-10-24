import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic
import Synthesis.RiemannG21ContinuumMomentStrictness

/-!
# G21 exact continuum moment symmetrization

For two height-response weights `A,P` and an increasing score `q`, define

  M0(A) = ∫ A,      MQ(A) = ∫ q A,
  M0(P) = ∫ P,      MQ(P) = ∫ q P.

The cross product

  M0(A) MQ(P) - MQ(A) M0(P)

has the exact symmetrized product-integral representation

  1/2 ∫∫ (q(v)-q(u)) (A(u)P(v)-A(v)P(u)).

This is the continuum identity that the Agda `StrictKernelMomentRatioExact`
owner previously carried only as an explicit producer field.  The proof uses
Mathlib's product-integral factorization and ordinary ring algebra.

Strict positivity still requires the literal taper specialization: global
nonnegativity of the symmetrized carrier plus strict positivity on a
positive-product-measure region.  That specialization is intentionally kept as
a separate same-object obligation.
-/

noncomputable section

open MeasureTheory Set

namespace Synthesis

variable {α : Type*} [MeasurableSpace α]

/-- Zeroth moment. -/
def moment0 (A : α → ℝ) (μ : Measure α) : ℝ :=
  ∫ x, A x ∂μ

/-- Score-weighted moment. -/
def momentQ (q A : α → ℝ) (μ : Measure α) : ℝ :=
  ∫ x, q x * A x ∂μ

/-- Symmetrized determinant carrier on the product space. -/
def symmetrizedMomentIntegrand
    (A P q : α → ℝ) (z : α × α) : ℝ :=
  (q z.2 - q z.1) *
    (A z.1 * P z.2 - A z.2 * P z.1)

/-- Integrability of the symmetrized carrier from the four one-variable
integrability hypotheses naturally present in the moment problem. -/
theorem integrable_symmetrizedMomentIntegrand
    {μ : Measure α} [SFinite μ]
    {A P q : α → ℝ}
    (hA : Integrable A μ) (hP : Integrable P μ)
    (hqA : Integrable (fun x => q x * A x) μ)
    (hqP : Integrable (fun x => q x * P x) μ) :
    Integrable (symmetrizedMomentIntegrand A P q) (μ.prod μ) := by
  have h1 : Integrable (fun z : α × α => A z.1 * (q z.2 * P z.2)) (μ.prod μ) :=
    hA.mul_prod hqP
  have h2 : Integrable (fun z : α × α => P z.1 * (q z.2 * A z.2)) (μ.prod μ) :=
    hP.mul_prod hqA
  have h3 : Integrable (fun z : α × α => (q z.1 * A z.1) * P z.2) (μ.prod μ) :=
    hqA.mul_prod hP
  have h4 : Integrable (fun z : α × α => (q z.1 * P z.1) * A z.2) (μ.prod μ) :=
    hqP.mul_prod hA
  have hfun : symmetrizedMomentIntegrand A P q =
      (fun z : α × α =>
        A z.1 * (q z.2 * P z.2)
        - P z.1 * (q z.2 * A z.2)
        - (q z.1 * A z.1) * P z.2
        + (q z.1 * P z.1) * A z.2) := by
    funext z
    unfold symmetrizedMomentIntegrand
    ring
  rw [hfun]
  exact ((h1.sub h2).sub h3).add h4

/-- Exact continuum symmetrization identity. -/
theorem integral_symmetrizedMomentIntegrand
    {μ : Measure α} [SFinite μ]
    {A P q : α → ℝ}
    (hA : Integrable A μ) (hP : Integrable P μ)
    (hqA : Integrable (fun x => q x * A x) μ)
    (hqP : Integrable (fun x => q x * P x) μ) :
    (∫ z, symmetrizedMomentIntegrand A P q z ∂(μ.prod μ)) =
      2 * (moment0 A μ * momentQ q P μ - momentQ q A μ * moment0 P μ) := by
  have h1 : Integrable (fun z : α × α => A z.1 * (q z.2 * P z.2)) (μ.prod μ) :=
    hA.mul_prod hqP
  have h2 : Integrable (fun z : α × α => P z.1 * (q z.2 * A z.2)) (μ.prod μ) :=
    hP.mul_prod hqA
  have h3 : Integrable (fun z : α × α => (q z.1 * A z.1) * P z.2) (μ.prod μ) :=
    hqA.mul_prod hP
  have h4 : Integrable (fun z : α × α => (q z.1 * P z.1) * A z.2) (μ.prod μ) :=
    hqP.mul_prod hA
  have hfun : symmetrizedMomentIntegrand A P q =
      (fun z : α × α =>
        A z.1 * (q z.2 * P z.2)
        - P z.1 * (q z.2 * A z.2)
        - (q z.1 * A z.1) * P z.2
        + (q z.1 * P z.1) * A z.2) := by
    funext z
    unfold symmetrizedMomentIntegrand
    ring
  rw [hfun]
  rw [integral_add ((h1.sub h2).sub h3) h4]
  rw [integral_sub (h1.sub h2) h3]
  rw [integral_sub h1 h2]
  rw [integral_prod_mul, integral_prod_mul, integral_prod_mul, integral_prod_mul]
  unfold moment0 momentQ
  ring

/-- Exact strict-continuum compiler.  Once the literal symmetrized carrier is
nonnegative everywhere and positive on a positive-product-measure subset, the
moment cross product is strictly positive. -/
theorem strictMomentCrossProduct_of_symmetrizedCarrier
    {μ : Measure α} [SFinite μ]
    {A P q : α → ℝ} {s : Set (α × α)}
    (hA : Integrable A μ) (hP : Integrable P μ)
    (hqA : Integrable (fun x => q x * A x) μ)
    (hqP : Integrable (fun x => q x * P x) μ)
    (hFnonneg : ∀ z, 0 <= symmetrizedMomentIntegrand A P q z)
    (hs : 0 < (μ.prod μ) s)
    (hFpos : ∀ z ∈ s, 0 < symmetrizedMomentIntegrand A P q z) :
    0 < moment0 A μ * momentQ q P μ - momentQ q A μ * moment0 P μ := by
  have hFint : Integrable (symmetrizedMomentIntegrand A P q) (μ.prod μ) :=
    integrable_symmetrizedMomentIntegrand hA hP hqA hqP
  have hint : 0 < ∫ z, symmetrizedMomentIntegrand A P q z ∂(μ.prod μ) :=
    integral_pos_of_nonneg_of_pos_on_posMeasure hFint hFnonneg hs hFpos
  have hid := integral_symmetrizedMomentIntegrand hA hP hqA hqP
  nlinarith

end Synthesis
