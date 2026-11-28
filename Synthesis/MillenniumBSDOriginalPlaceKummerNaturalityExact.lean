import Synthesis.MillenniumBSDOriginalPlaceSelmerShaExact

namespace BSDCohomology
open WeierstrassCurve CategoryTheory DASHI.BSD.OriginalH1
noncomputable section
universe u
variable {K : Type u} [Field K] [NumberField K]
variable (W : WeierstrassCurve K) [W.IsElliptic]

/-- Specialize the actual completion naturality square to every original
finite and infinite place, on the same maps used by Selmer. -/
theorem place_rationalKummer_natural
    (hsK : Function.Surjective (fun Q : GeometricPoint W => (2:ℕ) • Q))
    (hs : ∀ v : OriginalPlace K, Function.Surjective
      (fun Q : GeometricPoint (localCurve W v) => (2:ℕ) • Q))
    (v : OriginalPlace K) (P : BasePoint W) :
    placeTorsionLoc W v (rationalKummerClass W hsK P) =
      rationalKummerClass (localCurve W v) (hs v) (placeBasePoint W v P) := by
  exact actualCompletion_rationalKummer (L:=placeField K v) W hsK (hs v) P

end
end BSDCohomology
