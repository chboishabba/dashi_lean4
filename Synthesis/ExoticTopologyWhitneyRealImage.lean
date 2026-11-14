import Synthesis.ExoticTopologyWhitneySimons
import Mathlib.Tactic

/-!
# Whitney umbrella: EXACT real semialgebraic image

Completes the point-set algebraic positive direction from the new Whitney
native owner rather than copying a second parametrisation.

For P(u,v)=(uv,u,v²), the real image is precisely
  { (x,y,z) | x²=y²z and 0≤z }.
The implicit algebraic equation alone includes the spurious negative
z-axis. This result identifies the actual real point set, NOT its
subspace topology, smooth stratification, normality or Whitney
conditions. Source: classical Whitney umbrella / pinch point.
-/

namespace Synthesis.ExoticTopology

theorem whitney_realImage_iff (p : Point3) :
    (∃ u v : ℝ, whitneyParam u v = p) ↔
      whitneyPolynomial p = 0 ∧ 0 ≤ p.z := by
  constructor
  · rintro ⟨u, v, hp⟩
    rw [← hp]
    exact whitneyImage_necessary u v
  · rintro ⟨hpol, hz⟩
    have hsq : p.x ^ 2 = p.y ^ 2 * p.z := by
      dsimp [whitneyPolynomial] at hpol
      linarith
    by_cases hy : p.y = 0
    · have hx2 : p.x ^ 2 = 0 := by simpa [hy] using hsq
      have hx : p.x = 0 := (sq_eq_zero_iff).mp hx2
      refine ⟨0, Real.sqrt p.z, ?_⟩
      cases p with
      | mk x y z =>
        simp only [Point3.x, Point3.y, Point3.z] at hy hx hz ⊢
        simp [whitneyParam, hy, hx, Real.sq_sqrt hz]
    · have hv : (p.x / p.y) ^ 2 = p.z := by
        rw [div_pow, div_eq_iff (pow_ne_zero 2 hy)]
        nlinarith [hsq]
      have hmul : p.y * (p.x / p.y) = p.x := by
        field_simp [hy]
      refine ⟨p.y, p.x / p.y, ?_⟩
      cases p with
      | mk x y z =>
        simp only [Point3.x, Point3.y, Point3.z] at hv hmul ⊢
        simp [whitneyParam, hmul, hv]

end Synthesis.ExoticTopology
