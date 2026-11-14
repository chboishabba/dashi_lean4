import Synthesis.ExoticTopologyWhitneySimons
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-!
# A source-specific seashell parametric surface, with exact radial identity

D. von Seggern's classical seashell family, as tabulated in
Weisstein / MathWorld, is instantiated with n=a=b=1, c=1/10.
The original coordinate prescription includes a shrinking helical
radial contribution plus a fixed nonzero tube offset.

We reuse `Point3` from the Whitney/Simons Lean consumer, and
Mathlib's real sine/cosine theorems. This models an actual real
parametric set and its radius identity; it does NOT assert global
injectivity/immersion or smooth behaviour after arbitrary endpoint
identifications. No new general "surface" axioms are introduced.
-/

namespace Synthesis.ExoticTopology

noncomputable def seashellRadius (u v : ℝ) : ℝ :=
  (1 - v / (2 * Real.pi)) * (1 + Real.cos u) + (1 / 10 : ℝ)

noncomputable def seashellParam (u v : ℝ) : Point3 :=
  { x := seashellRadius u v * Real.cos v
    y := seashellRadius u v * Real.sin v
    z := v / (2 * Real.pi) +
      (1 - v / (2 * Real.pi)) * Real.sin u }

/-- Exact coordinate-level invariant x²+y²=radius². -/
theorem seashell_radial_identity (u v : ℝ) :
    (seashellParam u v).x ^ 2 + (seashellParam u v).y ^ 2 =
      seashellRadius u v ^ 2 := by
  dsimp [seashellParam]
  calc
    (seashellRadius u v * Real.cos v) ^ 2 +
        (seashellRadius u v * Real.sin v) ^ 2 =
      (seashellRadius u v) ^ 2 *
        (Real.sin v ^ 2 + Real.cos v ^ 2) := by ring
    _ = seashellRadius u v ^ 2 := by
      rw [Real.sin_sq_add_cos_sq]
      ring

/-- The source formula identifies the two endpoints of its u parameter.
    This is a parametric seam only; it is not a proof of a quotient
    manifold or of injectivity elsewhere. -/
theorem seashell_u_zero_two_pi (v : ℝ) :
    seashellParam 0 v = seashellParam (2 * Real.pi) v := by
  simp [seashellParam, seashellRadius, Real.sin_two_pi, Real.cos_two_pi]

end Synthesis.ExoticTopology
