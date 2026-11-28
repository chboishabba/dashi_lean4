import Synthesis.NavierStokesOriginalMeanAndTailExact
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace DASHI.NavierStokes.PhysicalMixed
open DASHI.NavierStokes.EuclideanMidpoint
open MeasureTheory
noncomputable section

/-- The actual longitudinal mode satisfies a homogeneous scalar ODE,
with no assumption of transversality at later times. -/
theorem actual_divergence_derivative (N : ℕ) (ν : ℝ)
    (U : Vec3 → ℝ → CVec3) (k : Vec3) (t : ℝ)
    (h : ∀ i, HasDerivAt (fun s => U k s i)
      (-((ν*massSq k : ℝ):ℂ)*U k t i+galerkinForce N U k t i) t) :
    HasDerivAt (fun s => outputDot k (U k s))
      (-((ν*massSq k : ℝ):ℂ)*outputDot k (U k t)) t := by
  have hf := actual_galerkin_force_transverse N U k t
  unfold outputDot at hf ⊢
  simp only [Fin.sum_univ_three] at hf ⊢
  convert (((h 0).const_mul (k 0:ℂ)).add
    ((h 1).const_mul (k 1:ℂ))).add ((h 2).const_mul (k 2:ℂ)) using 1 <;>
    linear_combination hf

/-- Integrating factor on the actual signed modal curve. -/
theorem actual_divergence_heat_identity (N : ℕ) (ν T : ℝ)
    (U : Vec3 → ℝ → CVec3) (k : Vec3)
    (hODE : ∀ t ∈ Set.uIcc 0 T, ∀ i,
      HasDerivAt (fun s => U k s i)
      (-((ν*massSq k : ℝ):ℂ)*U k t i+galerkinForce N U k t i) t) :
    (Real.exp (ν*massSq k*T):ℂ)*outputDot k (U k T)=
      outputDot k (U k 0) := by
  let a := ν*massSq k
  let f := fun t : ℝ => (Real.exp (a*t):ℂ)*outputDot k (U k t)
  have hd : ∀ t ∈ Set.uIcc 0 T, HasDerivAt f 0 t := by
    intro t ht
    have he := (((hasDerivAt_id t).const_mul a).exp).ofReal_comp
    have hu := actual_divergence_derivative N ν U k t (hODE t ht)
    convert he.mul hu using 1 <;> simp [f,a] <;> ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0:ℂ)) volume 0 T)
  have hf : f T=f 0 := sub_eq_zero.mp (by simpa using hi.symm)
  simpa [f,a] using hf

theorem actual_divergence_preserved (N : ℕ) (ν T : ℝ)
    (U : Vec3 → ℝ → CVec3) (k : Vec3)
    (hODE : ∀ t ∈ Set.uIcc 0 T, ∀ i,
      HasDerivAt (fun s => U k s i)
      (-((ν*massSq k : ℝ):ℂ)*U k t i+galerkinForce N U k t i) t)
    (h0 : outputDot k (U k 0)=0) :
    outputDot k (U k T)=0 := by
  have h := actual_divergence_heat_identity N ν T U k hODE
  rw [h0] at h
  exact (mul_eq_zero.mp h).resolve_left (by
    exact_mod_cast (Real.exp_ne_zero (ν*massSq k*T)))

end
end DASHI.NavierStokes.PhysicalMixed
