import Synthesis.MillenniumBSDCMClayPointKummerExact
import Synthesis.MillenniumBSDExplicitSelmerIntersection
import Synthesis.MillenniumBSDTwoDescentTautologicalModelFirewall
import Mathlib.Tactic

/-!
# CM Clay Selmer: literal all-place arithmetic fidelity

Unlike the tautological quotient-only exact sequence, the actual worked CM
Selmer carrier is the explicitly defined global square-class intersection:
  real signs compatible with the real Kummer image, AND
  localized square classes in the Q_p Kummer image for EVERY rational prime.

These theorems expose those concrete conditions from the SAME inhabitant
cmClayTwoDescentResidual used by the finite exact-sequence consequences.
-/

namespace Synthesis.Millennium.BSD

noncomputable section

/-- The actual worked Selmer carrier is definitionally the independently
defined explicit all-place square-class subgroup. -/
theorem cmClaySelmer_is_explicitAllPlace :
    (cmClayTwoDescentResidual).Selmer = explicitTwoSelmerSubgroup :=
  rfl

/-- Every element of the worked Selmer carrier satisfies the real-place
two-descent sign condition. -/
theorem cmClaySelmer_realCondition
    (s : (cmClayTwoDescentResidual).Selmer) :
    realKummerLocalization
      (s.1 : RatSquareClass × RatSquareClass) ∈ RealKummerImage :=
  s.property.1

/-- Every element of the worked Selmer carrier meets the actual Q_p Kummer
image for EVERY prime, not merely a user-selected finite test set. -/
theorem cmClaySelmer_everyFinitePlace
    (s : (cmClayTwoDescentResidual).Selmer)
    (p : Nat.Primes) :
    letI : Fact p.1.Prime := ⟨p.2⟩
    localizeKummerPair p.1
      (s.1 : RatSquareClass × RatSquareClass) ∈
        LocalKummerImage p.1 :=
  s.property.2 p

/-- The transported Clay-point Kummer image automatically satisfies BOTH
independently defined kinds of local admission. -/
theorem cmClayKummer_allPlaces
    (P : CMClayRationalPoint) :
    (realKummerLocalization
      ((cmClayGlobalKummerHom (Multiplicative.ofAdd P)).1 :
        RatSquareClass × RatSquareClass) ∈ RealKummerImage)
    ∧
    (∀ p : Nat.Primes,
      letI : Fact p.1.Prime := ⟨p.2⟩
      localizeKummerPair p.1
        ((cmClayGlobalKummerHom (Multiplicative.ofAdd P)).1 :
          RatSquareClass × RatSquareClass) ∈
          LocalKummerImage p.1) :=
  ⟨cmClaySelmer_realCondition _, cmClaySelmer_everyFinitePlace _⟩

/-!
This is what genuine all-place arithmetic looks like for the CM curve. The
next generalization must define and prove analogous conditions on the SAME
arbitrary rational elliptic curve, rather than merely construct some exact
sequence with its group of rational points. No Sha identification, stable-rank
control or universal analytic comparison follows here.
-/

end

end Synthesis.Millennium.BSD
