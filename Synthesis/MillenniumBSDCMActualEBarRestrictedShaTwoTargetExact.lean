import Synthesis.MillenniumBSDLocalKummerCohomologyReduction
import Synthesis.MillenniumBSDSelmerShaCohomologicalBoundary
import Mathlib.Tactic

/-!
# Selected CM curve: E(Qbar)-valued restricted-local Sha candidate

The repository ALREADY defines the actual geometric E(Qbar)
Galois coefficient module cmEllipticPointRepresentation and
the induced H1 map from the selected (Z/2)^2 representation.

This module specializes the actual rational global-to-local
cohomology kernel to those E(Qbar) coefficients. This fixes
the type error in the older EllipticShaTwoComparisonBoundary,
which used the E[2] representation as Sha coefficients.

CRITICAL remaining K2 interface:
The rationalTateShafarevichOne(A) construction restricts
the *global coefficient module* A to G_{Q_v}. To identify it
with the classical Tate–Shafarevich group one must prove
the local coefficient comparison with E(Qbar_v), plus
the selected geometric [2] long exact sequence.
Thus these objects are deliberately named RESTRICTED,
not classical Sha(E/Q). No fake equivalence or axiom.
-/

namespace Synthesis.Millennium.BSD

/-- Global continuous H¹ of the original E(Qbar) module
on y²=x³-x; this is NOT the four-point E[2] coefficient. -/
abbrev CMSelectedEllipticGlobalH1 :=
  ContinuousCohomology.continuousCohomology 1
    cmEllipticPointRepresentation

/-- Original E(Qbar)-coefficient global-to-rational-local
kernel, with local coefficients still restricted from
global E(Qbar). Classical local coefficient comparison OPEN. -/
noncomputable def cmSelectedEBarRestrictedShaOne :
    AddSubgroup CMSelectedEllipticGlobalH1 :=
  rationalTateShafarevichOne cmEllipticPointRepresentation

/-- Literal membership, actually evaluated in H¹(G_Q,E(Qbar)).
This is a genuine same-coefficient theorem, not E[2] H¹. -/
theorem cmSelectedEBarRestrictedShaOne_mem_iff
    (x : CMSelectedEllipticGlobalH1) :
    x ∈ cmSelectedEBarRestrictedShaOne ↔
      ∀ v : RationalPlace,
        (ContinuousCohomology.map
          (Field.absoluteGaloisGroup.map
            (algebraMap ℚ (rationalLocalField v)))
          (𝟙 _) 1).hom x = 0 := by
  exact mem_rationalTateShafarevichOne_iff
    cmEllipticPointRepresentation x

/-- The genuine E(Qbar)-COEFFICIENT 2-torsion subgroup
of that restricted global-to-local H¹ kernel.
Still not called classical Sha(E/Q)[2] without local
completion naturality. -/
noncomputable def cmSelectedEBarRestrictedShaTwo :
    AddSubgroup cmSelectedEBarRestrictedShaOne :=
  rationalTateShafarevichTwoTorsion cmEllipticPointRepresentation

theorem cmSelectedEBarRestrictedShaTwo_mem_iff
    (x : cmSelectedEBarRestrictedShaOne) :
    x ∈ cmSelectedEBarRestrictedShaTwo ↔
      (2 : ℕ) • x = 0 := by
  exact mem_rationalTateShafarevichTwoTorsion_iff
    cmEllipticPointRepresentation x

end Synthesis.Millennium.BSD
