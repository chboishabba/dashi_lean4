import Mathlib

/-!
# BSD arithmetic frontier: the literal `E[2]` Galois module of `y² = x³ - x`

This file pays, on the literal Mathlib carriers, the first item of the BSD
arithmetic min-cut recorded in the millennium handoff
(`PROGRAMME_FRONTIERS.md`): *actual elliptic `E[2]` same-object*.

The curve is the same object used by the handoff's BSD lane,

  `cmWeierstrass : WeierstrassCurve ℚ := ⟨0, 0, 0, -1, 0⟩`,  i.e. `y² = x³ - x`,

and the point group is Mathlib's own `WeierstrassCurve.Affine.Point` of the
base change of that very curve to an arbitrary field `F` of characteristic
zero — in particular to `AlgebraicClosure ℚ`.  Nothing here is a status
Boolean, a record of obligations, or a transported abstract carrier: every
statement below is about `(cmWeierstrass.baseChange F).toAffine.Point`.

What is proved:

* `cmBC_twoTorsion_classification`: a point of the base-changed curve is killed
  by `2` iff it is one of `0`, `(0,0)`, `(1,0)`, `(-1,0)`;
* `cmTwoTorsionEquiv`: an explicit additive isomorphism
  `ZMod 2 × ZMod 2 ≃+ E[2]` on Mathlib's 2-torsion subgroup, with the labelling
  used by the handoff's abstract `(ℤ/2)²` module;
* `cmBC_twoTorsion_galois_fixed`: every `ℚ`-algebra automorphism of `F` fixes
  every 2-torsion point, so the `G_ℚ`-action on `E[2]` is trivial;
* `cmTwoTorsionEquiv_galois_equivariant`: the isomorphism above is equivariant
  for the trivial action on `(ℤ/2)²` and the genuine coordinatewise action on
  the elliptic 2-torsion.

Remaining (not proved here, and not asserted anywhere below): the comparison of
`H¹(G_ℚ, E[2])` with `(ℚ*/(ℚ*)²)²`, of the explicit and cohomological Selmer
groups, and of the Selmer cokernel with `Ш(E/ℚ)[2]`.
-/

namespace Synthesis.Millennium.BSD

open WeierstrassCurve

/-- The congruent-number-style CM curve `y² = x³ - x` over `ℚ`, exactly the
carrier used by the handoff's BSD lane. -/
def cmWeierstrass : WeierstrassCurve ℚ := ⟨0, 0, 0, -1, 0⟩

theorem cmWeierstrass_discriminant : cmWeierstrass.Δ = 64 := by
  rw [cmWeierstrass, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  norm_num1

section BaseChange

variable (F : Type*) [Field F] [Algebra ℚ F] [DecidableEq F]

/-- Any field which is a `ℚ`-algebra has characteristic zero. -/
instance (priority := 100) cmCharZero : CharZero F :=
  charZero_of_injective_algebraMap (algebraMap ℚ F).injective

/-- The base change of `y² = x³ - x` to `F`. -/
noncomputable abbrev cmBC : WeierstrassCurve F := cmWeierstrass.baseChange F

instance cmBC_isElliptic : (cmBC F).IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff]
  have h : (cmBC F).Δ = algebraMap ℚ F cmWeierstrass.Δ := by
    simp [cmBC, WeierstrassCurve.baseChange]
  rw [h, cmWeierstrass_discriminant]
  simp

variable {F}

omit [DecidableEq F] in
theorem cmBC_equation_iff (x y : F) :
    (cmBC F).toAffine.Equation x y ↔ y ^ 2 = x ^ 3 - x := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [cmBC, cmWeierstrass, WeierstrassCurve.baseChange, WeierstrassCurve.map,
    map_zero, map_one, map_neg]
  constructor <;> intro h <;> linear_combination h

omit [DecidableEq F] in
theorem cmBC_nonsingular_iff (x y : F) :
    (cmBC F).toAffine.Nonsingular x y ↔ y ^ 2 = x ^ 3 - x := by
  rw [← WeierstrassCurve.Affine.equation_iff_nonsingular, cmBC_equation_iff]

omit [DecidableEq F] in
theorem cmBC_negY (x y : F) : (cmBC F).toAffine.negY x y = -y := by
  simp [WeierstrassCurve.Affine.negY, cmBC, cmWeierstrass, WeierstrassCurve.baseChange,
    WeierstrassCurve.map]

omit [DecidableEq F] in
/-- The three nonzero 2-torsion points are honest points of the curve. -/
theorem cmBC_nonsingular_zero : (cmBC F).toAffine.Nonsingular (0 : F) 0 := by
  rw [cmBC_nonsingular_iff]; ring

omit [DecidableEq F] in
theorem cmBC_nonsingular_one : (cmBC F).toAffine.Nonsingular (1 : F) 0 := by
  rw [cmBC_nonsingular_iff]; ring

omit [DecidableEq F] in
theorem cmBC_nonsingular_negOne : (cmBC F).toAffine.Nonsingular (-1 : F) 0 := by
  rw [cmBC_nonsingular_iff]; ring

/-- `(0,0)`. -/
noncomputable def cmP0 : (cmBC F).toAffine.Point := .some cmBC_nonsingular_zero
/-- `(1,0)`. -/
noncomputable def cmP1 : (cmBC F).toAffine.Point := .some cmBC_nonsingular_one
/-- `(-1,0)`. -/
noncomputable def cmPm1 : (cmBC F).toAffine.Point := .some cmBC_nonsingular_negOne

omit [DecidableEq F] in
/-- Every point with vanishing `y`-coordinate is its own negative. -/
theorem cmBC_neg_of_y_zero {x : F} (h : (cmBC F).toAffine.Nonsingular x 0) :
    -(.some h : (cmBC F).toAffine.Point) = .some h := by
  rw [WeierstrassCurve.Affine.Point.neg_some]
  congr 1
  simp [WeierstrassCurve.Affine.negY, cmWeierstrass]

theorem cmBC_two_nsmul_of_y_zero {x : F} (h : (cmBC F).toAffine.Nonsingular x 0) :
    (2 : ℕ) • (.some h : (cmBC F).toAffine.Point) = 0 := by
  rw [two_nsmul]
  exact add_eq_zero_iff_eq_neg.mpr (cmBC_neg_of_y_zero h).symm

/-- **Classification of the literal 2-torsion.**  A point of `y² = x³ - x`
over any characteristic-zero field is killed by `2` exactly when it is one of
the four rational points `0`, `(0,0)`, `(1,0)`, `(-1,0)`. -/
theorem cmBC_twoTorsion_classification (P : (cmBC F).toAffine.Point) :
    (2 : ℕ) • P = 0 ↔ P = 0 ∨ P = cmP0 ∨ P = cmP1 ∨ P = cmPm1 := by
  constructor
  · intro hP
    have hself : P = -P := by
      rw [two_nsmul] at hP
      exact add_eq_zero_iff_eq_neg.mp hP
    cases P with
    | zero => exact Or.inl rfl
    | @some x y h =>
        rw [WeierstrassCurve.Affine.Point.neg_some] at hself
        have hxy : x = x ∧ y = (cmBC F).toAffine.negY x y := by simpa using hself
        rw [cmBC_negY] at hxy
        have hy : y = 0 := by
          have h2 : (2 : F) * y = 0 := by linear_combination hxy.2
          rcases mul_eq_zero.mp h2 with h3 | h3
          · exact absurd h3 (by norm_num)
          · exact h3
        subst hy
        have heq := (cmBC_nonsingular_iff x 0).mp h
        have hfac : x * ((x - 1) * (x + 1)) = 0 := by linear_combination -heq
        rcases mul_eq_zero.mp hfac with h1 | h1
        · subst h1; exact Or.inr (Or.inl rfl)
        · rcases mul_eq_zero.mp h1 with h2 | h2
          · have : x = 1 := by linear_combination h2
            subst this; exact Or.inr (Or.inr (Or.inl rfl))
          · have : x = -1 := by linear_combination h2
            subst this; exact Or.inr (Or.inr (Or.inr rfl))
  · rintro (rfl | rfl | rfl | rfl)
    · simp
    · exact cmBC_two_nsmul_of_y_zero _
    · exact cmBC_two_nsmul_of_y_zero _
    · exact cmBC_two_nsmul_of_y_zero _

/-- The literal 2-torsion subgroup `E[2]` of the Mathlib point group. -/
def cmTwoTorsion (F : Type*) [Field F] [Algebra ℚ F] [DecidableEq F] :
    AddSubgroup (cmBC F).toAffine.Point where
  carrier := {P | (2 : ℕ) • P = 0}
  zero_mem' := by simp
  add_mem' := by
    intro P Q hP hQ
    change (2 : ℕ) • (P + Q) = 0
    change (2 : ℕ) • P = 0 at hP
    change (2 : ℕ) • Q = 0 at hQ
    rw [nsmul_add, hP, hQ, add_zero]
  neg_mem' := by
    intro P hP
    change (2 : ℕ) • P = 0 at hP
    change (2 : ℕ) • (-P) = 0
    rw [smul_neg, hP, neg_zero]

@[simp] theorem cmTwoTorsion_mem_iff (P : (cmBC F).toAffine.Point) :
    P ∈ cmTwoTorsion F ↔ (2 : ℕ) • P = 0 := Iff.rfl

theorem cmP0_two_nsmul : (2 : ℕ) • (cmP0 : (cmBC F).toAffine.Point) = 0 :=
  cmBC_two_nsmul_of_y_zero _

theorem cmP1_two_nsmul : (2 : ℕ) • (cmP1 : (cmBC F).toAffine.Point) = 0 :=
  cmBC_two_nsmul_of_y_zero _

theorem cmPm1_two_nsmul : (2 : ℕ) • (cmPm1 : (cmBC F).toAffine.Point) = 0 :=
  cmBC_two_nsmul_of_y_zero _

/-! ### The group law on the 2-torsion -/

/-- Two distinct points with vanishing `y`-coordinate add to the third one: the
line `y = 0` meets `y² = x³ - x` in the three 2-torsion points. -/
theorem cmBC_add_of_y_zero {x₁ x₂ : F} (h₁ : (cmBC F).toAffine.Nonsingular x₁ 0)
    (h₂ : (cmBC F).toAffine.Nonsingular x₂ 0)
    (h₃ : (cmBC F).toAffine.Nonsingular (-x₁ - x₂) 0) (hx : x₁ ≠ x₂) :
    (.some h₁ + .some h₂ : (cmBC F).toAffine.Point) = .some h₃ := by
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne hx]
  have hs : (cmBC F).toAffine.slope x₁ x₂ 0 0 = 0 := by
    rw [WeierstrassCurve.Affine.slope_of_X_ne hx]; simp
  congr 1 <;>
    simp [WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
      WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.negY, hs, cmWeierstrass]

theorem cmP0_add_cmP1 : (cmP0 + cmP1 : (cmBC F).toAffine.Point) = cmPm1 := by
  have h3 : (cmBC F).toAffine.Nonsingular (-(0 : F) - 1) 0 := by
    rw [cmBC_nonsingular_iff]; ring
  have h := cmBC_add_of_y_zero (cmBC_nonsingular_zero (F := F)) cmBC_nonsingular_one h3
    (by norm_num)
  rw [cmP0, cmP1, h, cmPm1]
  congr 1
  ring

theorem cmP0_add_cmPm1 : (cmP0 + cmPm1 : (cmBC F).toAffine.Point) = cmP1 := by
  have h3 : (cmBC F).toAffine.Nonsingular (-(0 : F) - (-1)) 0 := by
    rw [cmBC_nonsingular_iff]; ring
  have h := cmBC_add_of_y_zero (cmBC_nonsingular_zero (F := F)) cmBC_nonsingular_negOne h3
    (by norm_num)
  rw [cmP0, cmPm1, h, cmP1]
  congr 1
  ring

theorem cmP1_add_cmPm1 : (cmP1 + cmPm1 : (cmBC F).toAffine.Point) = cmP0 := by
  have h3 : (cmBC F).toAffine.Nonsingular (-(1 : F) - (-1)) 0 := by
    rw [cmBC_nonsingular_iff]; ring
  have h := cmBC_add_of_y_zero (cmBC_nonsingular_one (F := F)) cmBC_nonsingular_negOne h3
    (by norm_num)
  rw [cmP1, cmPm1, h, cmP0]
  congr 1
  ring

/-! ### The literal `(ℤ/2)²` structure of `E[2]` -/

/-- The additive hom `ZMod 2 →+ E(F)` determined by a point killed by `2`. -/
noncomputable def cmTorsionHom {P : (cmBC F).toAffine.Point} (hP : (2 : ℕ) • P = 0) :
    ZMod 2 →+ (cmBC F).toAffine.Point :=
  ZMod.lift 2 ⟨zmultiplesHom _ P, by
    simp only [Nat.cast_ofNat, zmultiplesHom_apply]
    rw [two_zsmul, ← two_nsmul] at *
    exact hP⟩

@[simp] theorem cmTorsionHom_one {P : (cmBC F).toAffine.Point} (hP : (2 : ℕ) • P = 0) :
    cmTorsionHom hP 1 = P := by
  have h : ((1 : ℤ) : ZMod 2) = 1 := by decide
  rw [cmTorsionHom, ← h, ZMod.lift_coe]
  simp

/-- The comparison map `(ℤ/2)² → E[2]`, sending the handoff's labels
`(1,0), (0,1), (1,1)` to the points `(0,0), (1,0), (-1,0)`. -/
noncomputable def cmTwoTorsionHom : (ZMod 2 × ZMod 2) →+ cmTwoTorsion F :=
  AddMonoidHom.codRestrict
    ((cmTorsionHom (cmP0_two_nsmul (F := F))).coprod (cmTorsionHom (cmP1_two_nsmul (F := F))))
    (cmTwoTorsion F) (by
      intro v
      show (2 : ℕ) • _ = 0
      rw [← map_nsmul]
      have h : (2 : ℕ) • v = 0 := by
        obtain ⟨a, b⟩ := v
        ext <;> revert a b <;> decide
      rw [h, map_zero])

theorem cmTwoTorsionHom_apply (a b : ZMod 2) :
    (cmTwoTorsionHom (F := F) (a, b) : (cmBC F).toAffine.Point)
      = cmTorsionHom (cmP0_two_nsmul (F := F)) a + cmTorsionHom (cmP1_two_nsmul (F := F)) b :=
  rfl

@[simp] theorem cmTwoTorsionHom_00 :
    (cmTwoTorsionHom (F := F) (0, 0) : (cmBC F).toAffine.Point) = 0 := by
  simp [cmTwoTorsionHom_apply]

@[simp] theorem cmTwoTorsionHom_10 :
    (cmTwoTorsionHom (F := F) (1, 0) : (cmBC F).toAffine.Point) = cmP0 := by
  simp [cmTwoTorsionHom_apply]

@[simp] theorem cmTwoTorsionHom_01 :
    (cmTwoTorsionHom (F := F) (0, 1) : (cmBC F).toAffine.Point) = cmP1 := by
  simp [cmTwoTorsionHom_apply]

@[simp] theorem cmTwoTorsionHom_11 :
    (cmTwoTorsionHom (F := F) (1, 1) : (cmBC F).toAffine.Point) = cmPm1 := by
  simp [cmTwoTorsionHom_apply, cmP0_add_cmP1]

theorem cmTwoTorsionHom_bijective : Function.Bijective (cmTwoTorsionHom (F := F)) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    rintro ⟨a, b⟩ hab
    have hv : ((cmTwoTorsionHom (F := F) (a, b) : cmTwoTorsion F) :
        (cmBC F).toAffine.Point) = 0 := by rw [hab]; rfl
    have hzmod : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
    rcases hzmod a with rfl | rfl <;> rcases hzmod b with rfl | rfl
    · rfl
    · rw [cmTwoTorsionHom_01] at hv
      exact absurd hv (WeierstrassCurve.Affine.Point.some_ne_zero _)
    · rw [cmTwoTorsionHom_10] at hv
      exact absurd hv (WeierstrassCurve.Affine.Point.some_ne_zero _)
    · rw [cmTwoTorsionHom_11] at hv
      exact absurd hv (WeierstrassCurve.Affine.Point.some_ne_zero _)
  · rintro ⟨P, hP⟩
    rw [cmTwoTorsion_mem_iff, cmBC_twoTorsion_classification] at hP
    rcases hP with rfl | rfl | rfl | rfl
    · exact ⟨(0, 0), by ext; simp⟩
    · exact ⟨(1, 0), by ext; simp⟩
    · exact ⟨(0, 1), by ext; simp⟩
    · exact ⟨(1, 1), by ext; simp⟩

/-- **`E[2] ≅ (ℤ/2)²` on the literal carriers.**  An additive isomorphism from
`ZMod 2 × ZMod 2` onto Mathlib's 2-torsion subgroup of the point group of
`y² = x³ - x` over `F`. -/
noncomputable def cmTwoTorsionEquiv : (ZMod 2 × ZMod 2) ≃+ cmTwoTorsion F :=
  AddEquiv.ofBijective _ (cmTwoTorsionHom_bijective (F := F))

@[simp] theorem cmTwoTorsionEquiv_apply (v : ZMod 2 × ZMod 2) :
    (cmTwoTorsionEquiv (F := F) v : (cmBC F).toAffine.Point)
      = (cmTwoTorsionHom (F := F) v : (cmBC F).toAffine.Point) := rfl

theorem cmTwoTorsion_card : Nat.card (cmTwoTorsion F) = 4 := by
  rw [← Nat.card_congr (cmTwoTorsionEquiv (F := F)).toEquiv]
  simp

/-! ### Triviality of the Galois action on `E[2]` -/

/-- The coordinatewise action of a `ℚ`-algebra automorphism of `F` on the
points of the base-changed curve. -/
noncomputable def cmGaloisAction (σ : F ≃ₐ[ℚ] F) :
    (cmBC F).toAffine.Point →+ (cmBC F).toAffine.Point :=
  WeierstrassCurve.Affine.Point.map (W' := cmWeierstrass.toAffine) (σ : F →ₐ[ℚ] F)

@[simp] theorem cmGaloisAction_cmP0 (σ : F ≃ₐ[ℚ] F) :
    cmGaloisAction σ (cmP0 : (cmBC F).toAffine.Point) = cmP0 := by
  rw [cmGaloisAction, cmP0, WeierstrassCurve.Affine.Point.map_some]
  congr 1 <;> simp

@[simp] theorem cmGaloisAction_cmP1 (σ : F ≃ₐ[ℚ] F) :
    cmGaloisAction σ (cmP1 : (cmBC F).toAffine.Point) = cmP1 := by
  rw [cmGaloisAction, cmP1, WeierstrassCurve.Affine.Point.map_some]
  congr 1 <;> simp

@[simp] theorem cmGaloisAction_cmPm1 (σ : F ≃ₐ[ℚ] F) :
    cmGaloisAction σ (cmPm1 : (cmBC F).toAffine.Point) = cmPm1 := by
  rw [cmGaloisAction, cmPm1, WeierstrassCurve.Affine.Point.map_some]
  congr 1 <;> simp

/-- **The `G_ℚ`-action on `E[2]` is trivial.**  Every `ℚ`-algebra automorphism
of `F` fixes every 2-torsion point of `y² = x³ - x`, because all four of them
are rational. -/
theorem cmBC_twoTorsion_galois_fixed (σ : F ≃ₐ[ℚ] F) {P : (cmBC F).toAffine.Point}
    (hP : (2 : ℕ) • P = 0) : cmGaloisAction σ P = P := by
  rcases (cmBC_twoTorsion_classification P).mp hP with rfl | rfl | rfl | rfl
  · exact map_zero _
  · exact cmGaloisAction_cmP0 σ
  · exact cmGaloisAction_cmP1 σ
  · exact cmGaloisAction_cmPm1 σ

/-- The comparison isomorphism `(ℤ/2)² ≅ E[2]` is Galois-equivariant for the
*trivial* action on `(ℤ/2)²`: the elliptic 2-torsion really is the constant
`(ℤ/2)²` Galois module. -/
theorem cmTwoTorsionEquiv_galois_equivariant (σ : F ≃ₐ[ℚ] F) (v : ZMod 2 × ZMod 2) :
    cmGaloisAction σ (cmTwoTorsionEquiv (F := F) v : (cmBC F).toAffine.Point)
      = (cmTwoTorsionEquiv (F := F) v : (cmBC F).toAffine.Point) :=
  cmBC_twoTorsion_galois_fixed σ (cmTwoTorsionEquiv (F := F) v).2

end BaseChange

/-! ### The case of interest: `F = AlgebraicClosure ℚ` -/

section Qbar

/-- An algebraic closure of `ℚ`; `Gal(Qbar/ℚ)` is the absolute Galois group. -/
abbrev Qbar := AlgebraicClosure ℚ

noncomputable instance : DecidableEq Qbar := Classical.decEq _

/-- Over `Qbar` the 2-torsion of `y² = x³ - x` consists exactly of the four
rational points `0`, `(0,0)`, `(1,0)`, `(-1,0)`. -/
theorem cmQbar_twoTorsion_classification (P : (cmBC Qbar).toAffine.Point) :
    (2 : ℕ) • P = 0 ↔ P = 0 ∨ P = cmP0 ∨ P = cmP1 ∨ P = cmPm1 :=
  cmBC_twoTorsion_classification P

/-- `E[2](Qbar) ≅ (ℤ/2)²`. -/
noncomputable def cmQbarTwoTorsionEquiv : (ZMod 2 × ZMod 2) ≃+ cmTwoTorsion Qbar :=
  cmTwoTorsionEquiv

/-- The absolute Galois group of `ℚ` acts trivially on `E[2](Qbar)`. -/
theorem cmQbar_twoTorsion_galois_trivial (σ : Qbar ≃ₐ[ℚ] Qbar)
    {P : (cmBC Qbar).toAffine.Point} (hP : (2 : ℕ) • P = 0) :
    cmGaloisAction σ P = P :=
  cmBC_twoTorsion_galois_fixed σ hP

/-! ### All geometric 2-torsion is already rational -/

/-- The base-change map on points, `E(ℚ) →+ E(Qbar)`, induced by `ℚ → Qbar`. -/
noncomputable def cmBaseChangeMap :
    (cmBC ℚ).toAffine.Point →+ (cmBC Qbar).toAffine.Point :=
  WeierstrassCurve.Affine.Point.map (W' := cmWeierstrass.toAffine)
    (Algebra.ofId ℚ Qbar : ℚ →ₐ[ℚ] Qbar)

@[simp] theorem cmBaseChangeMap_cmP0 : cmBaseChangeMap cmP0 = cmP0 := by
  rw [cmBaseChangeMap, cmP0, WeierstrassCurve.Affine.Point.map_some]
  congr 1
  all_goals simp

@[simp] theorem cmBaseChangeMap_cmP1 : cmBaseChangeMap cmP1 = cmP1 := by
  rw [cmBaseChangeMap, cmP1, WeierstrassCurve.Affine.Point.map_some]
  congr 1
  all_goals simp

@[simp] theorem cmBaseChangeMap_cmPm1 : cmBaseChangeMap cmPm1 = cmPm1 := by
  rw [cmBaseChangeMap, cmPm1, WeierstrassCurve.Affine.Point.map_some]
  congr 1
  all_goals simp

/-- **`E[2](ℚ) → E[2](Qbar)` is a bijection**: the whole geometric 2-torsion of
`y² = x³ - x` is defined over `ℚ`.  Together with
`cmQbar_twoTorsion_galois_trivial` this is the precise sense in which `E[2]` is
the constant `(ℤ/2)²` Galois module. -/
theorem cmBaseChangeMap_twoTorsion_bijOn :
    Set.BijOn cmBaseChangeMap {P : (cmBC ℚ).toAffine.Point | (2 : ℕ) • P = 0}
      {Q : (cmBC Qbar).toAffine.Point | (2 : ℕ) • Q = 0} := by
  refine ⟨?_, ?_, ?_⟩
  · intro P hP
    have : (2 : ℕ) • P = 0 := hP
    show (2 : ℕ) • cmBaseChangeMap P = 0
    rw [← map_nsmul, this, map_zero]
  · intro P _ Q _ hPQ
    exact WeierstrassCurve.Affine.Point.map_injective
      (f := (Algebra.ofId ℚ Qbar : ℚ →ₐ[ℚ] Qbar)) hPQ
  · intro Q hQ
    rcases (cmBC_twoTorsion_classification Q).mp hQ with rfl | rfl | rfl | rfl
    · exact ⟨0, by simp, map_zero _⟩
    · exact ⟨cmP0, cmP0_two_nsmul, cmBaseChangeMap_cmP0⟩
    · exact ⟨cmP1, cmP1_two_nsmul, cmBaseChangeMap_cmP1⟩
    · exact ⟨cmPm1, cmPm1_two_nsmul, cmBaseChangeMap_cmPm1⟩

end Qbar



end Synthesis.Millennium.BSD
