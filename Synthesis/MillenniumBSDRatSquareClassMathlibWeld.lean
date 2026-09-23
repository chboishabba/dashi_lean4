import Synthesis.MillenniumBSDSquareClassGroups
import Mathlib.RingTheory.DedekindDomain.SelmerGroup
import Mathlib.Algebra.GroupWithZero.Units.Equiv
import Mathlib.Tactic

/-!
# Same-object weld: repo rational square classes = mathlib K^x/(K^x)^2

The explicit descent machinery in this repository uses `RatSquareClass`, a
quotient of nonzero rationals by the cross-multiplied square relation.
Mathlib's computational Selmer implementation uses the canonical quotient

  Q^x / (Q^x)^2.

This file proves these are literally equivalent multiplicative groups.  After
this weld, the remaining BSD arithmetic same-object theorem is purely the
continuous Kummer isomorphism H^1(G_Q, mu_2) ~= Q^x/(Q^x)^2; there is no
additional ambiguity in the square-class carrier.
-/

namespace Synthesis.Millennium.BSD

abbrev MathlibRatSquareClass : Type :=
  ℚˣ ⧸ (powMonoidHom 2 : ℚˣ →* ℚˣ).range

def nonzeroRatOfUnit (u : ℚˣ) : NonzeroRat :=
  unitsEquivNeZero u

def unitOfNonzeroRat (q : NonzeroRat) : ℚˣ :=
  unitsEquivNeZero.symm q

@[simp] theorem nonzeroRatOfUnit_val (u : ℚˣ) :
    (nonzeroRatOfUnit u : ℚ) = u := rfl

@[simp] theorem unitOfNonzeroRat_val (q : NonzeroRat) :
    ((unitOfNonzeroRat q : ℚˣ) : ℚ) = q := rfl

noncomputable def mathlibSquareClassOf (q : NonzeroRat) :
    MathlibRatSquareClass :=
  QuotientGroup.mk' (powMonoidHom 2 : ℚˣ →* ℚˣ).range
    (unitOfNonzeroRat q)

theorem squareRel_mathlibSquareClass_eq
    {a b : NonzeroRat} (h : SquareRel a b) :
    mathlibSquareClassOf a = mathlibSquareClassOf b := by
  rw [QuotientGroup.eq_iff_div_mem]
  rcases h with ⟨s,t,hst⟩
  let u : ℚˣ := unitOfNonzeroRat
    ⟨(t : ℚ) / (s : ℚ), div_ne_zero t.property s.property⟩
  refine ⟨u, ?_⟩
  apply Units.ext
  change (a : ℚ) / (b : ℚ) = ((t : ℚ) / (s : ℚ)) ^ 2
  field_simp [a.property, b.property, s.property, t.property]
  nlinarith [hst]

noncomputable def ratSquareClassToMathlib :
    RatSquareClass → MathlibRatSquareClass :=
  Quotient.lift mathlibSquareClassOf
    (fun _ _ h => squareRel_mathlibSquareClass_eq h)

@[simp] theorem ratSquareClassToMathlib_mk (q : NonzeroRat) :
    ratSquareClassToMathlib (squareClassOf q) = mathlibSquareClassOf q := rfl

def unitToRatSquareClassHom : ℚˣ →* RatSquareClass where
  toFun := fun u => squareClassOf (nonzeroRatOfUnit u)
  map_one' := by
    apply Quotient.sound
    exact squareRel_of_eq (by ext; norm_num)
  map_mul' := by
    intro u v
    rw [← squareClassOf_mul]
    apply Quotient.sound
    apply squareRel_of_eq
    apply Subtype.ext
    rfl

theorem squareRange_le_unitToRatSquareClassHom_ker :
    (powMonoidHom 2 : ℚˣ →* ℚˣ).range ≤ unitToRatSquareClassHom.ker := by
  rintro x ⟨u,rfl⟩
  rw [MonoidHom.mem_ker]
  change squareClassOf (nonzeroRatOfUnit (u ^ 2)) = 1
  have hsq := ratSquareClass_sq_eq_one
    (squareClassOf (nonzeroRatOfUnit u))
  rw [← hsq]
  rw [← squareClassOf_mul]
  apply Quotient.sound
  apply squareRel_of_eq
  apply Subtype.ext
  rfl

noncomputable def mathlibSquareClassToRat :
    MathlibRatSquareClass →* RatSquareClass :=
  QuotientGroup.lift
    (powMonoidHom 2 : ℚˣ →* ℚˣ).range
    unitToRatSquareClassHom
    squareRange_le_unitToRatSquareClassHom_ker

@[simp] theorem mathlibSquareClassToRat_mk (u : ℚˣ) :
    mathlibSquareClassToRat
      (QuotientGroup.mk' (powMonoidHom 2 : ℚˣ →* ℚˣ).range u) =
      squareClassOf (nonzeroRatOfUnit u) := by
  exact QuotientGroup.lift_mk' _ _ _

theorem mathlibSquareClassToRat_leftInverse :
    Function.LeftInverse
      mathlibSquareClassToRat
      ratSquareClassToMathlib := by
  intro c
  refine Quotient.inductionOn c ?_
  intro q
  change squareClassOf
      (nonzeroRatOfUnit (unitOfNonzeroRat q)) = squareClassOf q
  congr
  exact unitsEquivNeZero.apply_symm_apply q

theorem mathlibSquareClassToRat_rightInverse :
    Function.RightInverse
      mathlibSquareClassToRat
      ratSquareClassToMathlib := by
  intro c
  refine QuotientGroup.induction_on c ?_
  intro u
  change mathlibSquareClassOf (nonzeroRatOfUnit u) =
    QuotientGroup.mk' (powMonoidHom 2 : ℚˣ →* ℚˣ).range u
  unfold mathlibSquareClassOf unitOfNonzeroRat nonzeroRatOfUnit
  rw [unitsEquivNeZero.symm_apply_apply]

noncomputable def ratSquareClassEquivMathlib :
    RatSquareClass ≃ MathlibRatSquareClass where
  toFun := ratSquareClassToMathlib
  invFun := mathlibSquareClassToRat
  left_inv := mathlibSquareClassToRat_leftInverse
  right_inv := mathlibSquareClassToRat_rightInverse

theorem ratSquareClassEquivMathlib_mk (q : NonzeroRat) :
    ratSquareClassEquivMathlib (squareClassOf q) =
      mathlibSquareClassOf q := rfl

/-- Multiplicative strengthening of the same-object square-class weld.  The
inverse map was already a MonoidHom; the forward map therefore preserves
multiplication by injectivity of that inverse. -/
noncomputable def ratSquareClassMulEquivMathlib :
    RatSquareClass ≃* MathlibRatSquareClass where
  toEquiv := ratSquareClassEquivMathlib
  map_mul' a b := by
    apply mathlibSquareClassToRat_rightInverse.injective
    simp [ratSquareClassEquivMathlib,
      mathlibSquareClassToRat_leftInverse]

/-- Pair-valued multiplicative same-object weld used by the E[2] Kummer lane. -/
noncomputable def ratKummerPairMulEquivMathlib :
    (RatSquareClass × RatSquareClass) ≃*
      (MathlibRatSquareClass × MathlibRatSquareClass) :=
  ratSquareClassMulEquivMathlib.prodCongr
    ratSquareClassMulEquivMathlib


/-- The same-object weld for the pair-valued 2-descent carrier. -/
noncomputable def ratKummerPairEquivMathlib :
    (RatSquareClass × RatSquareClass) ≃
      (MathlibRatSquareClass × MathlibRatSquareClass) :=
  ratSquareClassEquivMathlib.prodCongr ratSquareClassEquivMathlib

end Synthesis.Millennium.BSD
