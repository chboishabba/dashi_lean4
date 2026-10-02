import BSDCohomology.EllipticPointTopRep
import BSDCohomology.GenuineDegreeOneShaTwoTorsion

/-!
# Same-curve cohomological BSD targets

This module instantiates the actual current-Mathlib localization-kernel
construction with the genuine geometric elliptic-point Galois module
E(K̄). It also names the distinct E[2] H¹ ambient used by Kummer theory.

The distinction is essential:

  H¹(K,E[2])          -- Selmer/Kummer ambient
  H¹(K,E(K̄))         -- Weil-Châtelet ambient

and classical Sha(E) is the local-trivial subgroup of the SECOND object.
Its 2-torsion is then taken internally.

No x-T/Selmer comparison is assumed.
-/

namespace BSDCohomology

open ContinuousCohomology

noncomputable section

universe u v

variable {K : Type u} [Field K]
variable {V : Type v}
variable (places : V → Type u)
variable [∀ v, Field (places v)]
variable [∀ v, Algebra K (places v)]
variable (W : WeierstrassCurve K) [W.IsElliptic]

/-- Cohomological H¹ ambient for the literal elliptic two-torsion module. -/
abbrev EllipticTwoTorsionH1 :=
  continuousCohomology 1 (ellipticTwoTorsionTopRep W)

/-- Cohomological H¹ ambient for the literal geometric elliptic point module. -/
abbrev EllipticPointH1 :=
  continuousCohomology 1 (geometricPointTopRep W)

/-- Genuine degree-one localization kernel for the geometric elliptic point
module. This is the Mathlib Tate-Shafarevich construction specialized to
the same curve W. -/
abbrev EllipticSha :
    AddSubgroup (EllipticPointH1 W) :=
  DegreeOneSha places (geometricPointTopRep W)

/-- Genuine 2-torsion inside the actual degree-one elliptic Sha target. -/
abbrev EllipticShaTwoTorsion :
    AddSubgroup (EllipticSha places W) :=
  (nsmulAddMonoidHom (α := EllipticSha places W) 2).ker

/-- Membership in the specialized elliptic Sha target is exactly vanishing
of every current-Mathlib localization map. -/
theorem mem_ellipticSha_iff_allLocalizationsZero
    (x : EllipticPointH1 W) :
    x ∈ EllipticSha places W ↔
      ∀ v : V,
        (ContinuousCohomology.map
          (Field.absoluteGaloisGroup.map (algebraMap K (places v)))
          (𝟙 _) 1).hom x = 0 := by
  exact
    mem_degreeOneSha_iff_allLocalizationsZero
      places (geometricPointTopRep W) x

/-- The 2-primary finite-level target is defined internally, after local
triviality, rather than by confusing H¹(K,E[2]) with Sha(E)[2]. -/
theorem mem_ellipticShaTwoTorsion_iff
    (x : EllipticSha places W) :
    x ∈ EllipticShaTwoTorsion places W ↔
      2 • x = 0 := by
  rfl

/-!
BSD-C/D MAX-CUT NOW

Objects paid:
  * actual E(K̄) absolute-Galois representation;
  * actual E[2] absolute-Galois representation;
  * H¹(K,E[2]) ambient;
  * H¹(K,E(K̄)) ambient;
  * actual all-localization kernel Sha(E);
  * actual Sha(E)[2] subgroup.

Still open:
  * exact TopRep sequence 0 → E[2] → E(K̄) --[2]→ E(K̄);
  * connecting Kummer morphism E(K)/2E(K) → H¹(K,E[2]);
  * local Kummer compatibility;
  * Stoll x-T Selmer ≃ cohomological Selmer;
  * quotient comparison C₂(E) ≃ Sha(E)[2].
-/

end

end BSDCohomology
