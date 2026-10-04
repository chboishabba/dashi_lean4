import Mathlib
import Mathlib.MeasureTheory.Integral.Prod
import YangMills.IndependentBoundaryAverageRP
import YangMills.LiteralSU2BoundaryPlaneDoubleGaugeAverage
import YangMills.LiteralSU2BoundaryProjectedRPReduction

/-!
# Terminal finite pure-Wilson boundary-projected OS2 theorem

The source-specific work has reduced the literal one-boundary crossing average
to the independently gauged upper/lower boundary-plane Gram kernel.  The
remaining scalar `exp(-β |C|)` is strictly positive.  The generic independent-
boundary Fubini compiler therefore proves the averaged crossing kernel RP, and
the already-owned half-weight compiler closes the exact projected Wilson RP
statement.
-/

open MeasureTheory

namespace RequestProject.YangMills

/-- The scalar-free augmented plane exponential is integrable on two plane copies. -/
theorem su2_boundary_plane_feature_exponential_pair_integrable
    (n : ℕ) [NeZero n]
    (β : ℝ)
    (left right : SU2PositiveInteriorLinks n) :
    Integrable
      (fun bc : SU2BoundaryPlaneFields n × SU2BoundaryPlaneFields n =>
        Real.exp
          (β * finiteCrossPlaneFeatures
            (Finset.univ : Finset (SU2BoundaryPlaneCrossingFeatureIndex n))
            (fun _ => (1 : ℝ))
            (independentBoundaryFeature (su2BoundaryPlaneCrossingFeature n))
            (bc.1, left) (bc.2, right)))
      ((literalSU2BoundaryPlaneHaar n).prod
        (literalSU2BoundaryPlaneHaar n)) := by
  classical
  let terms : Finset (SU2BoundaryPlaneCrossingFeatureIndex n) := Finset.univ
  let feature := independentBoundaryFeature (su2BoundaryPlaneCrossingFeature n)
  let budget := finiteFeatureWeightBudget terms (fun _ => (1 : ℝ))
  refine Integrable.of_bound (by
      unfold finiteCrossPlaneFeatures feature independentBoundaryFeature
      fun_prop (disch := aesop))
    (Real.exp (|β| * budget))
    (Filter.Eventually.of_forall fun bc => ?_)
  rw [Real.norm_eq_abs, abs_exp]
  apply Real.exp_le_exp.mpr
  let K := finiteCrossPlaneFeatures terms (fun _ => (1 : ℝ)) feature
    (bc.1, left) (bc.2, right)
  calc
    β * K ≤ |β * K| := le_abs_self _
    _ = |β| * |K| := abs_mul β K
    _ ≤ |β| * budget := by
      gcongr
      exact finite_cross_plane_features_abs_le_budget
        terms (fun _ => (1 : ℝ)) feature
        (by intro i hi; norm_num)
        (by
          intro i hi z
          exact su2_boundary_plane_crossing_feature_abs_le_one
            n i z.1 z.2)
        (bc.1, left) (bc.2, right)

/--
The exact literal averaged crossing kernel is a positive scalar times the
generic independently boundary-averaged finite-feature exponential kernel.
-/
theorem literal_su2_boundary_averaged_crossing_eq_feature_average
    (n : ℕ) [NeZero n]
    (β : ℝ)
    (left right : SU2PositiveInteriorLinks n) :
    literalSU2BoundaryAveragedCrossingKernel n β left right =
      Real.exp (-(β * ((su2EvenTimeCrossingPlaquettes n).card : ℝ))) *
        independentBoundaryAveragedFeatureExponentialKernel
          (literalSU2BoundaryPlaneHaar n)
          (Finset.univ : Finset (SU2BoundaryPlaneCrossingFeatureIndex n))
          (fun _ => (1 : ℝ))
          (su2BoundaryPlaneCrossingFeature n)
          β left right := by
  rw [← literal_su2_boundary_plane_double_gauge_average_eq_literal]
  unfold literalSU2BoundaryPlaneAveragedDoubleGaugedCrossingKernel
  let terms : Finset (SU2BoundaryPlaneCrossingFeatureIndex n) := Finset.univ
  let feature := independentBoundaryFeature (su2BoundaryPlaneCrossingFeature n)
  let scalar := Real.exp (-(β * ((su2EvenTimeCrossingPlaquettes n).card : ℝ)))
  have hInt := su2_boundary_plane_feature_exponential_pair_integrable
    n β left right
  have hPoint :
      (fun bc : SU2BoundaryPlaneFields n × SU2BoundaryPlaneFields n =>
        su2BoundaryPlaneDoubleGaugedCrossingKernel n β left right bc.1 bc.2) =
      (fun bc => scalar *
        Real.exp
          (β * finiteCrossPlaneFeatures terms (fun _ => (1 : ℝ)) feature
            (bc.1, left) (bc.2, right))) := by
    funext bc
    unfold su2BoundaryPlaneDoubleGaugedCrossingKernel scalar terms feature
    rw [su2_boundary_plane_double_gauged_trace_eq_features]
  rw [hPoint]
  rw [integral_const_mul]
  congr 1
  rw [integral_prod _ hInt]
  unfold independentBoundaryAveragedFeatureExponentialKernel terms feature
  rfl

/-- Averaged literal crossing-kernel reflection positivity. -/
theorem literal_su2_boundary_averaged_crossing_rp :
    LiteralSU2BoundaryAveragedCrossingRPExact := by
  intro n hn β hβ f hfMeas hfInt
  letI : NeZero n := hn
  let scalar := Real.exp (-(β * ((su2EvenTimeCrossingPlaquettes n).card : ℝ)))
  let K0 := independentBoundaryAveragedFeatureExponentialKernel
    (literalSU2BoundaryPlaneHaar n)
    (Finset.univ : Finset (SU2BoundaryPlaneCrossingFeatureIndex n))
    (fun _ => (1 : ℝ))
    (su2BoundaryPlaneCrossingFeature n)
    β
  have h0 :
      0 ≤ ∫ left : SU2PositiveInteriorLinks n,
        ∫ right : SU2PositiveInteriorLinks n,
          f left * K0 left right * f right
          ∂(literalSU2PositiveInteriorHaar n)
        ∂(literalSU2PositiveInteriorHaar n) := by
    exact independent_boundary_feature_exponential_average_rp
      (literalSU2BoundaryPlaneHaar n)
      (literalSU2PositiveInteriorHaar n)
      (Finset.univ : Finset (SU2BoundaryPlaneCrossingFeatureIndex n))
      (fun _ => (1 : ℝ))
      (su2BoundaryPlaneCrossingFeature n)
      (by intro i hi; norm_num)
      (by
        intro i hi
        exact su2_boundary_plane_crossing_feature_measurable n i)
      (by
        intro i hi planes field
        exact su2_boundary_plane_crossing_feature_abs_le_one n i planes field)
      β hβ f hfMeas hfInt
  have hscalar : 0 ≤ scalar := (Real.exp_pos _).le
  have hscaled := mul_nonneg hscalar h0
  have hSame :
      ∀ left right : SU2PositiveInteriorLinks n,
        literalSU2BoundaryAveragedCrossingKernel n β left right =
          scalar * K0 left right := by
    intro left right
    exact literal_su2_boundary_averaged_crossing_eq_feature_average
      n β left right
  calc
    0 ≤ scalar *
        (∫ left : SU2PositiveInteriorLinks n,
          ∫ right : SU2PositiveInteriorLinks n,
            f left * K0 left right * f right
            ∂(literalSU2PositiveInteriorHaar n)
          ∂(literalSU2PositiveInteriorHaar n)) := hscaled
    _ = ∫ left : SU2PositiveInteriorLinks n,
        ∫ right : SU2PositiveInteriorLinks n,
          f left *
            literalSU2BoundaryAveragedCrossingKernel n β left right *
            f right
          ∂(literalSU2PositiveInteriorHaar n)
        ∂(literalSU2PositiveInteriorHaar n) := by
      simp_rw [hSame]
      simp_rw [← integral_const_mul]
      ring

/-- Terminal finite pure-Wilson boundary-Haar projected OS2 theorem. -/
theorem literal_su2_boundary_gauge_projection_rp_exact :
    LiteralSU2BoundaryGaugeProjectionRPExact :=
  literal_su2_boundary_gauge_projection_rp_of_averaged_crossing_rp
    literal_su2_boundary_averaged_crossing_rp

end RequestProject.YangMills
