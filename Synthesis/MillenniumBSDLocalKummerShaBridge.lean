import Synthesis.MillenniumBSDClassicalShaTwoBoundary
import Synthesis.MillenniumBSDLocalKummerCohomologyReduction
import Mathlib.RepresentationTheory.Homological.ContCohomology.Functoriality
import Mathlib.Tactic

/-!
# Bridge from local Kummer reduction to the prize-facing Sha class

The local cohomology reduction uses the generic trivial presentation of E[2],
while the prize-facing classical-Sha boundary reconstructs the same class
through the actual geometric E[2] representation.  This file proves those
constructions are the same and then transports the finite-place vanishing
theorems to the actual global elliptic H¹ class.
-/

namespace Synthesis.Millennium.BSD

open CategoryTheory

/-- The direct generic coefficient map to E(Qbar) is exactly the actual-E[2]
same-object map followed by the literal subgroup inclusion. -/
theorem globalGenericE2ToEllipticPoint_factor :
    globalGenericE2ToEllipticPoint =
      cmTwoTorsionTopRepToActual ≫ cmActualE2TopRepInclusion := by
  ext x
  rfl

/-- The induced global H¹ map therefore factors through actual E[2]. -/
theorem globalGenericE2H1ToEllipticPointH1_factor :
    globalGenericE2H1ToEllipticPointH1 =
      cmE2H1ToActual ≫ cmActualE2H1ToEllipticPointH1 := by
  rw [← ContinuousCohomology.map_comp]
  simpa [globalGenericE2H1ToEllipticPointH1, cmE2H1ToActual,
    cmActualE2H1ToEllipticPointH1, globalGenericE2ToEllipticPoint_factor]
    using
      (ContinuousCohomology.map_id
        (genericTwoTorsionRepresentation RationalAbsoluteGalois) 1).symm

/-- The generic square-class inverse used by the local lane is the same
generic inverse isolated in the low-degree coherence module. -/
theorem explicitSelmerToGenericTwoTorsionH1_eq_cmGeneric
    (s : explicitTwoSelmerSubgroup) :
    explicitSelmerToGenericTwoTorsionH1 s =
      (cmGenericTrivialE2H1MulEquivRatSquareClasses.symm s.1).toAdd := by
  rfl

/-- The actual geometric E[2] class attached to an explicit Selmer class is
the image of the generic trivial-E[2] reconstruction. -/
theorem cmExplicitSelmerClassToActualE2H1_eq_generic
    (s : explicitTwoSelmerSubgroup) :
    cmExplicitSelmerClassToActualE2H1 s =
      cmE2H1ToActual (explicitSelmerToGenericTwoTorsionH1 s) := by
  apply cmActualE2H1ToTrivial.injective
  rw [cmE2H1_maps_inverse_forward]
  rw [explicitSelmerToGenericTwoTorsionH1_eq_cmGeneric]
  exact cmActualE2H1ToTrivial_squareClass_inverse_coherence s.1

/-- Hence the local lane and the prize-facing Sha lane attach literally the
same global elliptic H¹ class to every explicit Selmer element. -/
theorem explicitSelmerGenericClassToEllipticH1_eq_prizeFacing
    (s : explicitTwoSelmerSubgroup) :
    explicitSelmerGenericClassToEllipticH1 s =
      cmExplicitSelmerClassToEllipticH1 s := by
  unfold explicitSelmerGenericClassToEllipticH1
  unfold cmExplicitSelmerClassToEllipticH1
  rw [globalGenericE2H1ToEllipticPointH1_factor,
    cmExplicitSelmerClassToActualE2H1_eq_generic]
  rfl

/-- Canonical p-adic restriction of the full elliptic-point H¹ class. -/
noncomputable def padicEllipticPointH1Restrict
    (p : ℕ) [Fact p.Prime] :
    ContinuousCohomology.continuousCohomology 1
        cmEllipticPointRepresentation ⟶
      ContinuousCohomology.continuousCohomology 1
        (padicRestrictedEllipticPointRepresentation p) :=
  ContinuousCohomology.map
    (padicAbsoluteGaloisRestriction p)
    (𝟙 (padicRestrictedEllipticPointRepresentation p)) 1

/-- The two coefficient-level routes from restricted generic E[2] to the
restricted full elliptic-point representation are literally equal. -/
theorem padicGenericE2ToRestrictedEllipticPoint_naturality
    (p : ℕ) [Fact p.Prime] :
    (TopRep.resFunctor
      (padicAbsoluteGaloisRestriction p :
        PadicAbsoluteGalois p →* RationalAbsoluteGalois)).map
        globalGenericE2ToEllipticPoint
      =
    genericTwoTorsionRestrictionHom
        (G := RationalAbsoluteGalois)
        (padicAbsoluteGaloisRestriction p)
      ≫
    padicGenericE2ToRestrictedEllipticPoint p := by
  ext x
  rfl

/-- Restriction commutes with the generic E[2] -> elliptic-point H¹ map. -/
theorem padicGenericE2EllipticH1_restriction_square
    (p : ℕ) [Fact p.Prime] :
    globalGenericE2H1ToEllipticPointH1 ≫
        padicEllipticPointH1Restrict p
      =
    genericTwoTorsionH1Restrict
        (G := RationalAbsoluteGalois)
        (padicAbsoluteGaloisRestriction p)
      ≫
        padicGenericE2H1ToEllipticPointH1 p := by
  rw [← ContinuousCohomology.map_comp,
    ← ContinuousCohomology.map_comp]
  rw [padicGenericE2ToRestrictedEllipticPoint_naturality]
  rfl

/-- Every finite explicit Selmer condition now implies vanishing of the
*prize-facing* elliptic H¹ class after p-adic restriction. -/
theorem cmExplicitSelmerClassToEllipticH1_padic_zero
    (hCompat :
      ∀ p : Nat.Primes,
        letI : Fact p.1.Prime := ⟨p.2⟩
        PadicQuadraticKummerCompatibility p.1)
    (hVan :
      ∀ p : Nat.Primes,
        letI : Fact p.1.Prime := ⟨p.2⟩
        PadicEllipticKummerImageVanishing p.1 (hCompat p))
    (s : explicitTwoSelmerSubgroup)
    (p : Nat.Primes) :
    letI : Fact p.1.Prime := ⟨p.2⟩
    padicEllipticPointH1Restrict p.1
      (cmExplicitSelmerClassToEllipticH1 s) = 0 := by
  letI : Fact p.1.Prime := ⟨p.2⟩
  rw [← explicitSelmerGenericClassToEllipticH1_eq_prizeFacing]
  unfold explicitSelmerGenericClassToEllipticH1
  have hsquare := padicGenericE2EllipticH1_restriction_square p.1
  have happ := congrArg
    (fun f => f.hom (explicitSelmerToGenericTwoTorsionH1 s)) hsquare
  have hzero :=
    explicitSelmer_finite_localizations_vanish_imageVanishing
      hCompat hVan s p
  simpa using happ.trans hzero

/-- Canonical restriction of the full elliptic-point H¹ class to the real
absolute Galois group. -/
noncomputable def realEllipticPointH1Restrict :
    ContinuousCohomology.continuousCohomology 1
        cmEllipticPointRepresentation ⟶
      ContinuousCohomology.continuousCohomology 1
        (TopRep.res
          (Field.absoluteGaloisGroup.map
            (algebraMap ℚ ℝ) :
              Field.absoluteGaloisGroup ℝ →*
                RationalAbsoluteGalois)
          cmEllipticPointRepresentation) :=
  ContinuousCohomology.map
    (Field.absoluteGaloisGroup.map (algebraMap ℚ ℝ))
    (𝟙 _) 1

/-- Exact infinite-place arithmetic owner.  The repo has already identified
the explicit real Kummer image as the equal-sign subgroup; what remains is
only to prove that those classes vanish after the local E[2] -> E(Qbar)
cohomology map. -/
structure RealEllipticKummerImageVanishing where
  equal_sign_maps_to_zero :
    ∀ c : RatSquareClass × RatSquareClass,
      realKummerLocalization c ∈ RealKummerImage →
        realEllipticPointH1Restrict
          (globalGenericE2H1ToEllipticPointH1
            ((cmGenericTrivialE2H1MulEquivRatSquareClasses.symm c).toAdd))
          = 0

/-- The explicit Selmer real condition therefore gives real-place vanishing
of the prize-facing class. -/
theorem cmExplicitSelmerClassToEllipticH1_real_zero
    (hReal : RealEllipticKummerImageVanishing)
    (s : explicitTwoSelmerSubgroup) :
    realEllipticPointH1Restrict
      (cmExplicitSelmerClassToEllipticH1 s) = 0 := by
  rw [← explicitSelmerGenericClassToEllipticH1_eq_prizeFacing]
  unfold explicitSelmerGenericClassToEllipticH1
  rw [explicitSelmerToGenericTwoTorsionH1_eq_cmGeneric]
  exact hReal.equal_sign_maps_to_zero s.1 s.2.1

/-- The full classical localization law is now reduced to one real-place
payment plus the two genuinely arithmetic finite-place Kummer families. -/
theorem cmExplicitSelmerClassToEllipticH1_localization_zero_of_real
    (hCompat :
      ∀ p : Nat.Primes,
        letI : Fact p.1.Prime := ⟨p.2⟩
        PadicQuadraticKummerCompatibility p.1)
    (hVan :
      ∀ p : Nat.Primes,
        letI : Fact p.1.Prime := ⟨p.2⟩
        PadicEllipticKummerImageVanishing p.1 (hCompat p))
    (hReal :
      ∀ s : explicitTwoSelmerSubgroup,
        (ContinuousCohomology.map
          (Field.absoluteGaloisGroup.map (algebraMap ℚ ℝ))
          (𝟙 _) 1).hom
          (cmExplicitSelmerClassToEllipticH1 s) = 0)
    (s : explicitTwoSelmerSubgroup) :
    cmExplicitSelmerClassToEllipticH1 s ∈
      classicalEllipticShaOne cmEllipticPointRepresentation := by
  rw [mem_rationalTateShafarevichOne_iff]
  intro v
  cases v with
  | infinite =>
      exact hReal s
  | padic p =>
      letI : Fact p.1.Prime := ⟨p.2⟩
      simpa [padicEllipticPointH1Restrict,
        padicAbsoluteGaloisRestriction,
        rationalLocalField] using
        cmExplicitSelmerClassToEllipticH1_padic_zero
          hCompat hVan s p




/-- Sharp all-place localization compiler: the only remaining inputs are the
scalar p-adic Kummer compatibility family, p-adic Kummer-image vanishing,
and the real equal-sign Kummer-image vanishing theorem. -/
theorem cmExplicitSelmerClassToEllipticH1_localization_zero_of_localKummer
    (hCompat :
      ∀ p : Nat.Primes,
        letI : Fact p.1.Prime := ⟨p.2⟩
        PadicQuadraticKummerCompatibility p.1)
    (hVan :
      ∀ p : Nat.Primes,
        letI : Fact p.1.Prime := ⟨p.2⟩
        PadicEllipticKummerImageVanishing p.1 (hCompat p))
    (hReal : RealEllipticKummerImageVanishing)
    (s : explicitTwoSelmerSubgroup) :
    cmExplicitSelmerClassToEllipticH1 s ∈
      classicalEllipticShaOne cmEllipticPointRepresentation := by
  rw [mem_rationalTateShafarevichOne_iff]
  intro v
  cases v with
  | infinite =>
      simpa [realEllipticPointH1Restrict, rationalLocalField] using
        cmExplicitSelmerClassToEllipticH1_real_zero hReal s
  | padic p =>
      letI : Fact p.1.Prime := ⟨p.2⟩
      simpa [padicEllipticPointH1Restrict,
        padicAbsoluteGaloisRestriction,
        rationalLocalField] using
        cmExplicitSelmerClassToEllipticH1_padic_zero
          hCompat hVan s p


/-- After local Kummer theory pays localization, only the two genuinely global
classical two-descent exactness laws remain. -/
structure ClassicalTwoDescentGlobalExactnessLaws where
  kernel_iff_globalKummerImage :
    ∀ s : explicitTwoSelmerSubgroup,
      cmExplicitSelmerClassToEllipticH1 s = 0 ↔
        s ∈ globalKummerImageSubgroup
  surjective_on_sha_two :
    ∀ x : classicalEllipticShaTwo cmEllipticPointRepresentation,
      ∃ s : explicitTwoSelmerSubgroup,
        cmExplicitSelmerClassToEllipticH1 s = x.1.1

/-- Local Kummer image theorems plus the two global exactness laws inhabit
the older three-law localization/exactness boundary. -/
noncomputable def classicalTwoDescentLocalizationExactnessLaws_of_localKummer
    (hCompat :
      ∀ p : Nat.Primes,
        letI : Fact p.1.Prime := ⟨p.2⟩
        PadicQuadraticKummerCompatibility p.1)
    (hVan :
      ∀ p : Nat.Primes,
        letI : Fact p.1.Prime := ⟨p.2⟩
        PadicEllipticKummerImageVanishing p.1 (hCompat p))
    (hReal : RealEllipticKummerImageVanishing)
    (hGlobal : ClassicalTwoDescentGlobalExactnessLaws) :
    ClassicalTwoDescentLocalizationExactnessLaws where
  localization_zero :=
    cmExplicitSelmerClassToEllipticH1_localization_zero_of_localKummer
      hCompat hVan hReal
  kernel_iff_globalKummerImage :=
    hGlobal.kernel_iff_globalKummerImage
  surjective_on_sha_two :=
    hGlobal.surjective_on_sha_two

/-- Max-cut prize-facing compiler from local Kummer theory and the two global
exactness laws directly to the fixed-representation classical Sha comparison. -/
theorem actualClassicalTwoDescentShaComparison_of_localKummer
    (hCompat :
      ∀ p : Nat.Primes,
        letI : Fact p.1.Prime := ⟨p.2⟩
        PadicQuadraticKummerCompatibility p.1)
    (hVan :
      ∀ p : Nat.Primes,
        letI : Fact p.1.Prime := ⟨p.2⟩
        PadicEllipticKummerImageVanishing p.1 (hCompat p))
    (hReal : RealEllipticKummerImageVanishing)
    (hGlobal : ClassicalTwoDescentGlobalExactnessLaws) :
    ActualClassicalTwoDescentShaComparison :=
  actualClassicalTwoDescentShaComparison_of_localizationExactness
    (classicalTwoDescentLocalizationExactnessLaws_of_localKummer
      hCompat hVan hReal hGlobal)

end Synthesis.Millennium.BSD
