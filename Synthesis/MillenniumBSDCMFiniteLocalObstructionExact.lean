import Synthesis.MillenniumBSDCMClaySelmerAllPlaceWitnessExact
import Synthesis.MillenniumBSDLocalKummerHomomorphism
import Synthesis.MillenniumBSDLocalSquareClass
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Tactic

/-!
# CM arithmetic local obstruction quotients on the literal Clay curve

For each genuine finite place p, use the ACTUAL image of the p-adic Kummer
map on E : y² = x³ - x. The obstruction of a global rational square-class
pair is its localization modulo that independently computed local image.

  Obs_p = ((Q_p*/Q_p*²)²) / image(Kummer_p)

A class has vanishing obstruction precisely when its localization satisfies
the p-adic Selmer condition. This is canonical on the worked curve: no
arbitrary Residual group, and no chosen abstract exact-sequence witness.

The real-place sign condition stays SEPARATE. Joint zero obstruction at all
primes plus the real condition is exactly the previously defined explicit
Selmer subgroup. Nothing identifies this obstruction quotient with Sha[2].
-/

namespace Synthesis.Millennium.BSD

noncomputable section

/-- Actual local square-class pair modulo the image of the local p-adic
Kummer homomorphism on the worked CM elliptic curve. -/
abbrev CMFiniteLocalObstructionGroup (p : Nat.Primes) : Type := by
  letI : Fact p.1.Prime := ⟨p.2⟩
  exact
    (PadicSquareClass p.1 × PadicSquareClass p.1)
      ⧸ localKummerImageSubgroup p.1

/-- Localize a global square-class pair and project to the quotient by
genuine locally realizable Kummer classes. -/
noncomputable def cmFiniteLocalObstruction (p : Nat.Primes) :
    (RatSquareClass × RatSquareClass) →*
      CMFiniteLocalObstructionGroup p := by
  letI : Fact p.1.Prime := ⟨p.2⟩
  exact
    (QuotientGroup.mk' (localKummerImageSubgroup p.1)).comp
      (localizeKummerPairHom p.1)

/-- Zero obstruction is exactly the genuine finite-place Kummer condition.
This equivalence is not supplied as an assumption of an exactness record. -/
theorem cmFiniteLocalObstruction_eq_one_iff
    (p : Nat.Primes)
    (c : RatSquareClass × RatSquareClass) :
    cmFiniteLocalObstruction p c = 1 ↔
      (letI : Fact p.1.Prime := ⟨p.2⟩
       localizeKummerPair p.1 c ∈ LocalKummerImage p.1) := by
  letI : Fact p.1.Prime := ⟨p.2⟩
  change
    QuotientGroup.mk' (localKummerImageSubgroup p.1)
      (localizeKummerPair p.1 c) = 1 ↔
      localizeKummerPair p.1 c ∈ LocalKummerImage p.1
  rw [QuotientGroup.eq_one_iff]
  rfl

/-- The independently defined Selmer subgroup is exactly the global classes
whose real sign condition holds and whose local quotient obstruction
vanishes at EVERY rational prime. -/
theorem cmSelmer_iff_real_and_allFiniteObstructionsZero
    (c : RatSquareClass × RatSquareClass) :
    c ∈ explicitTwoSelmerSubgroup ↔
      realKummerLocalization c ∈ RealKummerImage ∧
      ∀ p : Nat.Primes, cmFiniteLocalObstruction p c = 1 := by
  constructor
  · intro hc
    refine ⟨hc.1, ?_⟩
    intro p
    exact (cmFiniteLocalObstruction_eq_one_iff p c).2 (hc.2 p)
  · rintro ⟨hreal, hfinite⟩
    refine ⟨hreal, ?_⟩
    intro p
    exact (cmFiniteLocalObstruction_eq_one_iff p c).1 (hfinite p)

/-- Same curve throughout: the Mathlib Clay-facing CM point Kummer map has
zero obstruction at EVERY finite place. -/
theorem cmClayKummer_allFiniteObstructionsVanish
    (P : CMClayRationalPoint)
    (p : Nat.Primes) :
    cmFiniteLocalObstruction p
      ((cmClayGlobalKummerHom (Multiplicative.ofAdd P)).1 :
        RatSquareClass × RatSquareClass) = 1 := by
  apply (cmFiniteLocalObstruction_eq_one_iff p _).2
  exact
    cmClaySelmer_everyFinitePlace
      (cmClayGlobalKummerHom (Multiplicative.ofAdd P)) p

/-- Its real-place condition remains independently witnessed. -/
theorem cmClayKummer_realAndFiniteObstructions
    (P : CMClayRationalPoint) :
    realKummerLocalization
      ((cmClayGlobalKummerHom (Multiplicative.ofAdd P)).1 :
        RatSquareClass × RatSquareClass) ∈ RealKummerImage
    ∧
    ∀ p : Nat.Primes,
      cmFiniteLocalObstruction p
        ((cmClayGlobalKummerHom (Multiplicative.ofAdd P)).1 :
          RatSquareClass × RatSquareClass) = 1 :=
  ⟨cmClaySelmer_realCondition
      (cmClayGlobalKummerHom (Multiplicative.ofAdd P)),
    cmClayKummer_allFiniteObstructionsVanish P⟩

/-!
This is a same-curve arithmetic local/fibre construction. No 3^k or 9-sheet
fibre was substituted for a genuine local Galois-cohomological object.

Open tasks:
* generic E/Q local Kummer maps (not only y²=x³-x);
* actual global H¹ and Selmer as the kernel of local obstruction maps;
* canonical Sha(E)[2] identification;
* p-power towers and independent analytic-rank inequalities.
-/

end

end Synthesis.Millennium.BSD
