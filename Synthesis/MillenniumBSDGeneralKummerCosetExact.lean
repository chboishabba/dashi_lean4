import Synthesis.MillenniumBSDGeneralGeometricDoublingExact
import Synthesis.MillenniumBSDShorKummerFibreExact

/-!
The actual geometric doubling producer now discharges the selected
surjectivity assumption in the *rational* Kummer same-coset theorem.
The two kernels are kept distinct: E[2](Kbar) for geometric doubling,
and 2E(K) for equality of rational Kummer classes.
-/
namespace BSDCohomology
open WeierstrassCurve
noncomputable section

variable {K : Type*} [Field K] [CharZero K]
variable (W : WeierstrassCurve K) [W.IsElliptic]

/-- Full geometric choice is supplied by the existing general quartic
construction, rather than an extra hypothesis on this theorem. -/
theorem general_rationalKummer_sameCoset (P R : BasePoint W) :
    rationalKummerClass W (general_geometric_doubling_onto W) P =
      rationalKummerClass W (general_geometric_doubling_onto W) R ↔
      ∃ S : BasePoint W, (2 : ℕ) • S = P-R := by
  exact rationalKummer_sameCoset W
    (general_geometric_doubling_onto W) P R

/-- The actual rational Kummer class is zero precisely on the original
rational doubles; geometric halves over Kbar do not replace rational
halves over K. -/
theorem general_rationalKummer_zero_iff_double (P : BasePoint W) :
    rationalKummerClass W (general_geometric_doubling_onto W) P = 0 ↔
      ∃ S : BasePoint W, (2 : ℕ) • S = P := by
  simpa using (rationalKummerClass_zero_iff_double W
    (general_geometric_doubling_onto W) P)

end
end BSDCohomology
