import Synthesis.MillenniumBSDReductionPointCountWeld
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Tactic

/-!
# The literal odd-prime reduction is exactly y² = x³ - x over ZMod p

The previous file removed the chosen-minimal-model ambiguity.  Here we remove
the final residue-field representation ambiguity.

The displayed p-adic equation comes from the literal integral model
(0,0,0,-1,0) over Z_p.  Its reduction, transported across mathlib's actual
ring equivalence

  ResidueField Z_p ≃+* ZMod p,

is definitionally the same five-coefficient Weierstrass equation over ZMod p.
We also give the generic equation-point equivalence induced by a ring
equivalence, so affine solution counts are preserved exactly.
-/

namespace Synthesis.Millennium.BSD

open WeierstrassCurve
open IsLocalRing

def cmPadicIntegralWeierstrass
    (p : ℕ) [Fact p.Prime] :
    WeierstrassCurve ℤ_[p] :=
  ⟨0, 0, 0, -1, 0⟩

def cmZModWeierstrass
    (p : ℕ) [Fact p.Prime] :
    WeierstrassCurve (ZMod p) :=
  ⟨0, 0, 0, -1, 0⟩

theorem cmPadicIntegral_baseChange
    (p : ℕ) [Fact p.Prime] :
    (cmPadicIntegralWeierstrass p).baseChange ℚ_[p] =
      cmPadicWeierstrass p := by
  ext <;> simp [cmPadicIntegralWeierstrass,
    cmPadicWeierstrass, cmWeierstrass]

theorem cmPadic_integralModel_eq_literal
    (p : ℕ) [Fact p.Prime] :
    WeierstrassCurve.integralModel ℤ_[p]
      (cmPadicWeierstrass p)
      =
    cmPadicIntegralWeierstrass p := by
  apply WeierstrassCurve.map_injective
    (f := algebraMap ℤ_[p] ℚ_[p])
    (IsFractionRing.injective ℤ_[p] ℚ_[p])
  rw [WeierstrassCurve.baseChange_integralModel_eq
        ℤ_[p] (cmPadicWeierstrass p)]
  exact (cmPadicIntegral_baseChange p).symm

theorem cmLiteralReduction_eq_map_integral
    (p : ℕ) [Fact p.Prime] :
    (cmPadicWeierstrass p).reduction ℤ_[p]
      =
    (cmPadicIntegralWeierstrass p).map
      (IsLocalRing.residue ℤ_[p]) := by
  unfold WeierstrassCurve.reduction
  rw [cmPadic_integralModel_eq_literal]

theorem cmLiteralReduction_transport_to_ZMod
    (p : ℕ) [Fact p.Prime] :
    ((cmPadicWeierstrass p).reduction ℤ_[p]).map
      (padicResidueEquivZMod p).toRingHom
      =
    cmZModWeierstrass p := by
  rw [cmLiteralReduction_eq_map_integral]
  ext <;>
    simp [cmPadicIntegralWeierstrass,
      cmZModWeierstrass, padicResidueEquivZMod,
      PadicInt.residueField]

theorem cmZMod_equation_iff
    {p : ℕ} [Fact p.Prime]
    (x y : ZMod p) :
    (cmZModWeierstrass p).toAffine.Equation x y ↔
      y ^ 2 = x ^ 3 - x := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [cmZModWeierstrass]
  ring_nf

def mapAffineEquationPointEquiv
    {F K : Type*} [Field F] [Field K]
    (e : F ≃+* K)
    (W : WeierstrassCurve F) :
    AffineEquationPoint W ≃
      AffineEquationPoint (W.map e.toRingHom) where
  toFun := fun P =>
    ⟨(e P.1.1, e P.1.2),
      WeierstrassCurve.Affine.Equation.map
        e.toRingHom P.2⟩
  invFun := fun P =>
    ⟨(e.symm P.1.1, e.symm P.1.2), by
      have h :=
        WeierstrassCurve.Affine.Equation.map
          e.symm.toRingHom P.2
      simpa using h⟩
  left_inv := by
    intro P
    apply Subtype.ext
    simp
  right_inv := by
    intro P
    apply Subtype.ext
    simp

theorem mapAffineEquationPoint_card
    {F K : Type*} [Field F] [Field K]
    [Fintype F] [Fintype K]
    (e : F ≃+* K)
    (W : WeierstrassCurve F) :
    Fintype.card (AffineEquationPoint W) =
      Fintype.card
        (AffineEquationPoint (W.map e.toRingHom)) :=
  Fintype.card_congr (mapAffineEquationPointEquiv e W)

theorem literalReduction_affine_card_eq_ZMod
    (p : ℕ) [Fact p.Prime] :
    Fintype.card
      (AffineEquationPoint
        ((cmPadicWeierstrass p).reduction ℤ_[p]))
      =
    Fintype.card
      (AffineEquationPoint
        (cmZModWeierstrass p)) := by
  calc
    Fintype.card
      (AffineEquationPoint
        ((cmPadicWeierstrass p).reduction ℤ_[p]))
      =
    Fintype.card
      (AffineEquationPoint
        (((cmPadicWeierstrass p).reduction ℤ_[p]).map
          (padicResidueEquivZMod p).toRingHom)) :=
      mapAffineEquationPoint_card
        (padicResidueEquivZMod p)
        ((cmPadicWeierstrass p).reduction ℤ_[p])
    _ =
    Fintype.card
      (AffineEquationPoint (cmZModWeierstrass p)) := by
      rw [cmLiteralReduction_transport_to_ZMod]

end Synthesis.Millennium.BSD
