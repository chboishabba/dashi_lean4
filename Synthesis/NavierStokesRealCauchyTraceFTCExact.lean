import Synthesis.NavierStokesFractionalR568EndpointWeldExact
import Mathlib

/-!
Real-time proof of the R291/R596/R597 Cauchy trace. Coordinates are the
six real components of the ORIGINAL complex three-vector double-mixed
cell. A finite index enumerates the literal fixed-output ordered
incidences (including zero-valued cells). Rate is constant in time:
r_a = nu (|p_a|²+|q_a|²); positive on nonzero output.
The actual Galerkin cell ODE must instantiate the supplied derivative
hypothesis with R388/R560 data. No arbitrary-data uniform bound is asserted.
-/
namespace DASHI.NavierStokes.RealCauchyTrace
open MeasureTheory
open scoped BigOperators

private theorem derivative_finset_sum {J : Type*} (s : Finset J)
    (f : J → ℝ → ℝ) (d : J → ℝ) (t : ℝ)
    (h : ∀ i ∈ s, HasDerivAt (f i) (d i) t) :
    HasDerivAt (fun x => ∑ i ∈ s, f i x) (∑ i ∈ s, d i) t := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (hasDerivAt_const t (0:ℝ))
  | @insert i s hi ih =>
    have hd := (h i (Finset.mem_insert_self i s)).add
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))
    simpa [Finset.sum_insert hi] using hd

variable {I : Type*} [Fintype I]
abbrev Coord := Fin 6
abbrev PairCoord (I : Type*) := (I × I) × Coord
def cellProduct (m : I → Coord → ℝ → ℝ) (p : PairCoord I) (t : ℝ) :=
  m p.1.1 p.2 t * m p.1.2 p.2 t

def cauchyPair (r : I → ℝ) (m : I → Coord → ℝ → ℝ)
    (p : PairCoord I) (t : ℝ) :=
  2 * cellProduct m p t / (r p.1.1+r p.1.2)

def nonlinearPair (r : I → ℝ) (m f : I → Coord → ℝ → ℝ)
    (p : PairCoord I) (t : ℝ) :=
  2 * (f p.1.1 p.2 t * m p.1.2 p.2 t +
    m p.1.1 p.2 t * f p.1.2 p.2 t) / (r p.1.1+r p.1.2)

noncomputable def Q (r : I → ℝ) (m : I → Coord → ℝ → ℝ) (t : ℝ) :=
  ∑ p : PairCoord I, cauchyPair r m p t

noncomputable def H (m : I → Coord → ℝ → ℝ) (t : ℝ) :=
  ∑ p : PairCoord I, cellProduct m p t

noncomputable def F (r : I → ℝ) (m f : I → Coord → ℝ → ℝ) (t : ℝ) :=
  (∑ p : PairCoord I, nonlinearPair r m f p t) / 4

/-- R291 product rule on genuine real time; the same forcing appears
in the derivative and the weighted pair, including its sign. -/
theorem pair_derivative (r : I → ℝ) (m f : I → Coord → ℝ → ℝ)
    (hr : ∀ i, 0 < r i) (p : PairCoord I) (t : ℝ)
    (hm : ∀ i c, HasDerivAt (m i c) (-r i * m i c t + f i c t) t) :
    HasDerivAt (cauchyPair r m p)
      (nonlinearPair r m f p t - 2*cellProduct m p t) t := by
  have h := ((hm p.1.1 p.2).mul (hm p.1.2 p.2)).const_mul 2
  have hd := h.div_const (r p.1.1+r p.1.2)
  have hn : r p.1.1+r p.1.2 ≠ 0 := ne_of_gt (add_pos (hr _) (hr _))
  convert hd using 1
  unfold nonlinearPair cellProduct
  field_simp [hn] <;> ring

/-- Actual finite coherent trace derivative, without assuming it as an
opaque scalar equality. The same index and fixed Cauchy rate are used
throughout. The R597 H norm-square is the full ordered sum here. -/
theorem coherent_trace_derivative (r : I → ℝ) (m f : I → Coord → ℝ → ℝ)
    (hr : ∀ i, 0 < r i) (t : ℝ)
    (hm : ∀ i c, HasDerivAt (m i c) (-r i * m i c t + f i c t) t) :
    HasDerivAt (Q r m) (4*F r m f t-2*H m t) t := by
  classical
  have hd := derivative_finset_sum (Finset.univ : Finset (PairCoord I))
    (cauchyPair r m) (fun p => nonlinearPair r m f p t - 2*cellProduct m p t) t
    (fun p _ => pair_derivative r m f hr p t hm)
  convert hd using 1
  unfold F H
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

/-- R597 full Gram = square of the coherent fold, in real coordinates.
This shows H is nonnegative without dropping off-diagonal terms. -/
theorem coherent_H_nonnegative (m : I → Coord → ℝ → ℝ) (t : ℝ) :
    0 ≤ H m t := by
  classical
  unfold H cellProduct
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_nonneg
  intro c _
  rw [Fintype.sum_prod_type]
  have he : (∑ a : I, ∑ b : I, m a c t * m b c t) =
      (∑ a : I, m a c t)^2 := by
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
  rw [he]
  exact sq_nonneg _

/-- Real FTC on the physical finite trace, not abstract Time→Q integration.
The interval integrability hypotheses are on the same finite source;
they follow from smooth Galerkin cell and forcing curves. -/
theorem coherent_trace_FTC (r : I → ℝ) (m f : I → Coord → ℝ → ℝ)
    (hr : ∀ i, 0 < r i) (T : ℝ)
    (hm : ∀ t ∈ Set.uIcc 0 T, ∀ i c,
      HasDerivAt (m i c) (-r i * m i c t + f i c t) t)
    (hF : IntervalIntegrable (F r m f) volume 0 T)
    (hH : IntervalIntegrable (H m) volume 0 T) :
    4*(∫ t in 0..T, F r m f t) =
      Q r m T-Q r m 0+2*(∫ t in 0..T, H m t) := by
  have hd : ∀ t ∈ Set.uIcc 0 T,
      HasDerivAt (Q r m) (4*F r m f t-2*H m t) t :=
    fun t ht => coherent_trace_derivative r m f hr t (hm t ht)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((hF.const_mul 4).sub (hH.const_mul 2))
  rw [intervalIntegral.integral_sub (hF.const_mul 4) (hH.const_mul 2),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hi
  linarith

/-- Consume the actual trace in the existing direct R568 endpoint BIDI.
The signed physical upper remains the independent estimate. -/
theorem direct_R568_iff_trace (r : I → ℝ) (m f : I → Coord → ℝ → ℝ)
    (hr : ∀ i, 0 < r i) (T B : ℝ)
    (hm : ∀ t ∈ Set.uIcc 0 T, ∀ i c,
      HasDerivAt (m i c) (-r i * m i c t + f i c t) t)
    (hF : IntervalIntegrable (F r m f) volume 0 T)
    (hH : IntervalIntegrable (H m) volume 0 T) :
    4*(∫ t in 0..T, F r m f t) ≤ B ↔
      Q r m T+2*(∫ t in 0..T, H m t) ≤ B+Q r m 0 :=
  FractionalEndpoint.original_R568_C1_iff_positive_trace _ _ _ _ B
    (coherent_trace_FTC r m f hr T hm hF hH)

end DASHI.NavierStokes.RealCauchyTrace
