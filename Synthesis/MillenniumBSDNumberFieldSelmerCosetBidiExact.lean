import Synthesis.MillenniumBSDNumberFieldSelmerShaOriginalWeldExact
import Synthesis.MillenniumBSDGeneralKummerCosetExact

/-!
The original rational-point double-coset geometry, the number-field
Selmer inclusion and the original Sha map now form ONE same-object
bidirectional sequence. All objects are the original curve over K,
not synthetic square-class or finite-field replacement carriers.
-/
namespace BSDCohomology
open WeierstrassCurve
noncomputable section
universe u
variable {K : Type u} [Field K] [NumberField K]
variable (W : WeierstrassCurve K) [W.IsElliptic]

/-- Two actual rational points define the SAME original Selmer class
exactly when their difference is a double of a rational point.
No spurious geometric half over Kbar is treated as rational. -/
theorem numberFieldKummerSelmer_sameCoset
    (P R : BasePoint W) :
    numberFieldKummerToSelmer W P =
      numberFieldKummerToSelmer W R ↔
      ∃ S : BasePoint W, (2 : ℕ) • S = P - R := by
  change (⟨rationalKummerClass W (globalHalfOnto W) P,
      globalKummer_mem_selmer W (globalHalfOnto W)
        (localHalfOnto W) P⟩ :
      numberFieldSelmerTwo W) =
    ⟨rationalKummerClass W (globalHalfOnto W) R,
      globalKummer_mem_selmer W (globalHalfOnto W)
        (localHalfOnto W) R⟩ ↔ _
  rw [Subtype.mk.injEq]
  exact general_rationalKummer_sameCoset W P R

/-- Actual Selmer kernel/image transport on the same source:
a Selmer class has trivial image in the original point-Sha subgroup
exactly when it comes from a global rational point. -/
theorem numberFieldSelmerSha_zero_iff_globalKummer
    (z : numberFieldSelmerTwo W) :
    selmerToShaTwo W (globalHalfOnto W) (localHalfOnto W) z = 0 ↔
      ∃ P : BasePoint W, numberFieldKummerToSelmer W P = z := by
  rw [← AddMonoidHom.mem_ker]
  rw [numberField_selmerToSha_kernel]
  exact AddSubgroup.mem_range

end
end BSDCohomology
