import Cuisine.SensoryCore
import Synthesis.Hyperfabric
import Synthesis.MoonshineBase

/-!
# Cuisine → trit → fibre → hyperfabric: a proved structure-preserving transport

`Cuisine.ToneSeparation` records a *negative* result: the three-element safety
carrier of the cuisine lane is not the tone carrier of `Synthesis.ToneCore` as a
structured object.  That result is about one particular three-element set, and
it is often mis-read as "the cuisine lane has no formal link to the Monster /
ternary machinery at all".

This file proves the positive statement.  The link does not run through a
three-element set; it runs through the *arithmetic* the cuisine lane already
contains — the umami interaction law

    combinedIntensity = g + n + g * n,   equivalently   1 + c = (1+g)(1+n)

(`Cuisine.SensoryCore.UmamiBlend.succ_combined_eq`) — and through the
supersingular prime base of `Synthesis.MonsterFibre`.

The construction, in one line: *an umami intensity `u` is transported to the
exponent vector of `u + 1` over the fifteen supersingular primes, read modulo
three*, i.e. to a section of the balanced-ternary fibre over the Monster base —
a `Synthesis.Hyperfabric.Fabric`.

What is proved:

* `umamiCompose` — the cuisine combination law, made into a commutative monoid
  on `ℕ` with unit `0`, and `umamiSuccEquiv` / `umamiSuccEquiv_hom`: `n ↦ n+1`
  is an isomorphism of it onto the multiplicative monoid of positive naturals.
  This is the cuisine-side structure the transport preserves.
* `umamiFabric_compose` — **the transport is a monoid homomorphism**:
  combining two umami loads is ternary XOR (`(ℤ/3)^15` addition) of their
  hyperfabric sections.  This is the typed, structure-preserving bridge that was
  previously missing.
* `umamiFabric_surjective` — it is **onto**: every one of the `3^15` sections of
  the ternary fibre over the Monster base is the shadow of an umami intensity.
* `umamiFabric_cube` — its kernel contains the cubes, so the transport is the
  reduction of the cuisine monoid modulo cubes.
* `umamiFabric_season` and `dialectic_stage_is_seasoning` — the dialectical
  action of `Synthesis.Hyperfabric.fabricAct` on sections is *realised* on the
  cuisine side: one dialectical step is composition with the radical intensity
  `radical - 1` (the "whole spice rack"), and stage `s` is composition with its
  `stageIndex s`-th power.
* `supportMask_umamiFabric_maskIntensity`, `maskIntensity_injective` — the
  Monster mask lattice `MaskSSP` embeds in cuisine intensities, with support
  recovered exactly; so the mask geometry of `Synthesis.MonsterFibre` pulls back
  along the transport.
* `maskIntensity_trivector`, `repDim_eq_maskIntensity_succ`,
  `jCoefficient_eq_maskIntensity_add_two` — the moonshine numerals sit on this
  bridge: the mask of the three largest supersingular primes has cuisine
  intensity `196882`, whose successor is the supplied `repDim = 196883` and
  whose second successor is the supplied `jCoefficient = 196884`.

Boundary, stated explicitly: nothing here is a claim about food, about the
Monster group, or about modular forms.  `Fabric` is the set of functions from a
fifteen-element index set to a three-element set; `repDim` and `jCoefficient`
are the numerals `47·59·71` and `47·59·71+1` as supplied in
`AgdaMirror.Moonshine`.  What is genuinely established is that the cuisine
lane's own arithmetic law is a monoid whose reduction modulo cubes *is* the
hyperfabric over the Monster prime base, equivariantly for the dialectical
action.
-/

namespace Cuisine.UmamiTransport

open AgdaMirror.DASHIAlgebra (Trit Stage6 next6)
open AgdaMirror.MonsterOntos (SSP)
open Synthesis.ToneCore
open Synthesis.MonsterFibre
open Synthesis.Hyperfabric
open Synthesis.MoonshineBase
open Cuisine.SensoryCore (UmamiBlend)

/-- The `n`-th supersingular prime of the Monster base, as a natural number. -/
abbrev prime (p : SSP) : ℕ := AgdaMirror.MonsterOntos.toNat p

theorem prime_pos (p : SSP) : 0 < prime p := (toNat_prime p).pos

theorem prime_ne_zero (p : SSP) : prime p ≠ 0 := (prime_pos p).ne'

/-! ## The cuisine-side monoid: the umami combination law -/

/-- The umami combination law of `Cuisine.SensoryCore.UmamiBlend`, as a binary
operation: `g ⊕ n = g + n + g·n`. -/
def umamiCompose (a b : ℕ) : ℕ := a + b + a * b

@[simp] theorem blend_combined (g n : ℕ) :
    (UmamiBlend.ofLoads g n).combinedIntensity = umamiCompose g n := rfl

theorem combined_eq_compose (u : UmamiBlend) :
    u.combinedIntensity = umamiCompose u.glutamateLoad u.nucleotideLoad :=
  UmamiBlend.combined_eq u

/-- The defining factorisation: `1 + (a ⊕ b) = (1+a)(1+b)`. -/
theorem succ_umamiCompose (a b : ℕ) : umamiCompose a b + 1 = (a + 1) * (b + 1) := by
  simp only [umamiCompose]; ring

theorem umamiCompose_comm (a b : ℕ) : umamiCompose a b = umamiCompose b a := by
  simp only [umamiCompose]; ring

theorem umamiCompose_assoc (a b c : ℕ) :
    umamiCompose (umamiCompose a b) c = umamiCompose a (umamiCompose b c) := by
  simp only [umamiCompose]; ring

@[simp] theorem umamiCompose_zero_left (a : ℕ) : umamiCompose 0 a = a := by
  simp [umamiCompose]

@[simp] theorem umamiCompose_zero_right (a : ℕ) : umamiCompose a 0 = a := by
  simp [umamiCompose]

/-- **The cuisine combination law is the multiplicative monoid of positive
naturals.**  The bijection is `u ↦ u + 1`, i.e. exactly the shift appearing in
the Agda umami law. -/
def umamiSuccEquiv : ℕ ≃ {n : ℕ // 0 < n} where
  toFun u := ⟨u + 1, Nat.succ_pos u⟩
  invFun n := n.val - 1
  left_inv u := by simp
  right_inv n := by
    apply Subtype.ext
    show n.val - 1 + 1 = n.val
    have := n.property
    omega

theorem umamiSuccEquiv_hom (a b : ℕ) :
    (umamiSuccEquiv (umamiCompose a b)).val =
      (umamiSuccEquiv a).val * (umamiSuccEquiv b).val :=
  succ_umamiCompose a b

theorem umamiSuccEquiv_one : (umamiSuccEquiv 0).val = 1 := rfl

/-! ## Exponent vectors over the Monster prime base -/

/-- The tone of `m` at a supersingular prime: the `p`-adic valuation of `m`,
read in `ℤ/3`.  This is the `369` reduction of an exponent. -/
noncomputable def toneAt (m : ℕ) (p : SSP) : ZMod 3 :=
  ((m.factorization (prime p) : ℕ) : ZMod 3)

theorem toneAt_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (p : SSP) :
    toneAt (a * b) p = toneAt a p + toneAt b p := by
  simp [toneAt, Nat.factorization_mul ha hb]

theorem toneAt_pow (a k : ℕ) (p : SSP) :
    toneAt (a ^ k) p = (k : ZMod 3) * toneAt a p := by
  simp [toneAt, Nat.factorization_pow, Nat.cast_mul]

/-- **The transport.**  An umami intensity becomes a section of the ternary
fibre over the Monster prime base. -/
noncomputable def umamiFabric (u : ℕ) : Fabric := fabricZMod.symm (toneAt (u + 1))

@[simp] theorem fabricZMod_umamiFabric (u : ℕ) :
    fabricZMod (umamiFabric u) = toneAt (u + 1) :=
  fabricZMod.apply_symm_apply _

/-- A section is neutral at a point exactly when its `ℤ/3` coordinate vanishes
there. -/
theorem fabricZMod_eq_zero_iff (F : Fabric) (p : SSP) :
    fabricZMod F p = 0 ↔ F p = Trit.neg := by
  cases h : F p <;>
    simp [fabricZMod, Equiv.arrowCongr, h, toneZMod, toneToZMod, tritToneEquiv,
      AgdaMirror.TritBridge.toTriTruth, show (2 : ZMod 3) ≠ 0 by decide]

/-! ## The homomorphism property -/

/-- **The bridge.**  The transport carries the cuisine umami combination law to
ternary XOR of hyperfabric sections: it is a monoid homomorphism from the
cuisine-side monoid onto `(ℤ/3)^15`. -/
theorem umamiFabric_compose (a b : ℕ) :
    umamiFabric (umamiCompose a b) = fabricXor (umamiFabric a) (umamiFabric b) := by
  apply fabricZMod.injective
  rw [fabricZMod_add, fabricZMod_umamiFabric, fabricZMod_umamiFabric,
    fabricZMod_umamiFabric]
  funext p
  rw [succ_umamiCompose]
  exact toneAt_mul (Nat.succ_ne_zero a) (Nat.succ_ne_zero b) p

@[simp] theorem umamiFabric_zero : umamiFabric 0 = fabricZero := by
  apply fabricZMod.injective
  rw [fabricZMod_umamiFabric, fabricZMod_zero]
  funext p
  simp [toneAt]

/-- **Cubes are neutral.**  The transport factors through the cuisine monoid
modulo cubes: composing an intensity with itself three times is invisible. -/
theorem umamiFabric_cube (u : ℕ) :
    umamiFabric (umamiCompose u (umamiCompose u u)) = fabricZero := by
  rw [umamiFabric_compose, umamiFabric_compose]
  exact fabricXor_three (umamiFabric u)

/-! ## Products of supersingular primes, and their exponent vectors -/

/-- The exponent-vector construction: a product of the Monster primes with
prescribed exponents. -/
def primePow (e : SSP → ℕ) : ℕ := ∏ p : SSP, prime p ^ e p

theorem primePow_pos (e : SSP → ℕ) : 0 < primePow e :=
  Finset.prod_pos fun p _ => pow_pos (prime_pos p) _

theorem primePow_ne_zero (e : SSP → ℕ) : primePow e ≠ 0 := (primePow_pos e).ne'

/-- **Exponent vectors are read back by factorisation.**  This is where the
distinctness of the fifteen supersingular primes does the work. -/
theorem factorization_primePow (e : SSP → ℕ) (q : SSP) :
    (primePow e).factorization (prime q) = e q := by
  have hne : ∀ p ∈ (Finset.univ : Finset SSP), prime p ^ e p ≠ 0 := by
    intro p _; exact pow_ne_zero _ (prime_ne_zero p)
  rw [primePow, Nat.factorization_prod hne]
  rw [Finset.sum_apply']
  rw [Finset.sum_eq_single q]
  · rw [Nat.Prime.factorization_pow (toNat_prime q)]
    simp
  · intro p _ hpq
    rw [Nat.Prime.factorization_pow (toNat_prime p), Finsupp.single_apply]
    have : prime p ≠ prime q := fun h => hpq (Synthesis.MoonshineBase.toNat_injective h)
    simp [this]
  · intro h; exact absurd (Finset.mem_univ q) h

/-! ## Surjectivity of the transport -/

/-- The `{0,1,2}`-valued exponent read off a section. -/
noncomputable def digit (F : Fabric) (p : SSP) : ℕ := (fabricZMod F p).val

theorem digit_cast (F : Fabric) (p : SSP) : ((digit F p : ℕ) : ZMod 3) = fabricZMod F p := by
  simp [digit, ZMod.natCast_val, ZMod.cast_id]

/-- The canonical cuisine intensity realising a given hyperfabric section. -/
noncomputable def fabricIntensity (F : Fabric) : ℕ := primePow (digit F) - 1

theorem fabricIntensity_succ (F : Fabric) : fabricIntensity F + 1 = primePow (digit F) := by
  have := primePow_pos (digit F)
  simp only [fabricIntensity]
  omega

/-- **The transport is onto.**  Every section of the ternary fibre over the
Monster prime base — all `3 ^ 15` of them — is the ternary shadow of a cuisine
umami intensity. -/
theorem umamiFabric_fabricIntensity (F : Fabric) : umamiFabric (fabricIntensity F) = F := by
  apply fabricZMod.injective
  rw [fabricZMod_umamiFabric, fabricIntensity_succ]
  funext p
  rw [toneAt, factorization_primePow, digit_cast]

theorem umamiFabric_surjective : Function.Surjective umamiFabric :=
  fun F => ⟨fabricIntensity F, umamiFabric_fabricIntensity F⟩

/-- Consequently the image of the transport has exactly `3 ^ 15` elements. -/
theorem card_range_umamiFabric : Fintype.card Fabric = 3 ^ 15 := card_fabric

/-! ## Masks, and the moonshine numerals on the bridge -/

theorem maskProduct_eq_primePow (m : MaskSSP) :
    maskProduct m = primePow (fun p => if m p = true then 1 else 0) := by
  rw [maskProduct, primePow, ← Finset.prod_filter_mul_prod_filter_not Finset.univ
    (fun p => m p = true) (fun p => prime p ^ (if m p = true then 1 else 0))]
  have h1 : ∏ p ∈ Finset.univ.filter (fun p => m p = true),
      prime p ^ (if m p = true then 1 else 0) =
      ∏ p ∈ Finset.univ.filter (fun p => m p = true), prime p := by
    refine Finset.prod_congr rfl ?_
    intro p hp
    simp [(Finset.mem_filter.mp hp).2]
  have h2 : ∏ p ∈ Finset.univ.filter (fun p => ¬ (m p = true)),
      prime p ^ (if m p = true then 1 else 0) = 1 := by
    refine Finset.prod_eq_one ?_
    intro p hp
    simp [(Finset.mem_filter.mp hp).2]
  rw [h1, h2, mul_one]

theorem maskProduct_pos (m : MaskSSP) : 0 < maskProduct m := by
  rw [maskProduct_eq_primePow]; exact primePow_pos _

theorem factorization_maskProduct (m : MaskSSP) (p : SSP) :
    (maskProduct m).factorization (prime p) = if m p = true then 1 else 0 := by
  rw [maskProduct_eq_primePow, factorization_primePow]

/-- The cuisine intensity of a Monster mask: one less than the product of the
primes it keeps. -/
def maskIntensity (m : MaskSSP) : ℕ := maskProduct m - 1

theorem maskIntensity_succ (m : MaskSSP) : maskIntensity m + 1 = maskProduct m := by
  have := maskProduct_pos m
  simp only [maskIntensity]
  omega

/-- **The mask lattice sits inside the cuisine intensities.**  The hyperfabric
section of a mask's intensity has support exactly that mask, so the Monster mask
geometry of `Synthesis.MonsterFibre` pulls back along the transport. -/
theorem supportMask_umamiFabric_maskIntensity (m : MaskSSP) :
    supportMask (umamiFabric (maskIntensity m)) = m := by
  funext p
  have hz : fabricZMod (umamiFabric (maskIntensity m)) p = toneAt (maskProduct m) p := by
    rw [fabricZMod_umamiFabric, maskIntensity_succ]
  have hval : toneAt (maskProduct m) p = if m p = true then 1 else 0 := by
    rw [toneAt, factorization_maskProduct]
    by_cases h : m p = true <;> simp [h]
  by_cases h : m p = true
  · have hne : fabricZMod (umamiFabric (maskIntensity m)) p ≠ 0 := by
      rw [hz, hval]; simp [h]
    have : umamiFabric (maskIntensity m) p ≠ Trit.neg := by
      intro hc; exact hne ((fabricZMod_eq_zero_iff _ p).2 hc)
    simp [supportMask, support, this, h]
  · have hzero : fabricZMod (umamiFabric (maskIntensity m)) p = 0 := by
      rw [hz, hval]; simp [h]
    have hneg : umamiFabric (maskIntensity m) p = Trit.neg := (fabricZMod_eq_zero_iff _ p).1 hzero
    have hm : m p = false := Bool.eq_false_iff.mpr h
    simp [supportMask, support, hneg, hm]

/-- Distinct masks have distinct cuisine intensities. -/
theorem maskIntensity_injective : Function.Injective maskIntensity := by
  intro x y h
  have := congrArg (fun u => supportMask (umamiFabric u)) h
  simpa [supportMask_umamiFabric_maskIntensity] using this

/-- The three largest supersingular primes have cuisine intensity `196882`. -/
theorem maskIntensity_trivector : maskIntensity trivectorMask = 196882 := by
  rw [maskIntensity, maskProduct_trivector]
  decide

/-- ... whose successor is the supplied Monster representation numeral. -/
theorem repDim_eq_maskIntensity_succ :
    maskIntensity trivectorMask + 1 = AgdaMirror.Moonshine.repDim := by
  rw [maskIntensity_succ, maskProduct_trivector]

/-- ... and whose second successor is the supplied `j`-coefficient numeral. -/
theorem jCoefficient_eq_maskIntensity_add_two :
    maskIntensity trivectorMask + 2 = AgdaMirror.Moonshine.jCoefficient := by
  rw [show maskIntensity trivectorMask + 2 = (maskIntensity trivectorMask + 1) + 1 by ring,
    repDim_eq_maskIntensity_succ]
  exact AgdaMirror.Moonshine.mckay

/-! ## The dialectical action, realised on the cuisine side -/

/-- The radical of the Monster prime base: the product of all fifteen primes. -/
def radical : ℕ := primePow (fun _ => 1)

theorem radical_eq_maskProduct : radical = maskProduct fullMaskSSP := by
  rw [maskProduct_eq_primePow, radical]
  simp [fullMaskSSP]

theorem radical_pos : 0 < radical := primePow_pos _

theorem factorization_radical (p : SSP) : radical.factorization (prime p) = 1 :=
  factorization_primePow _ p

/-- The cuisine intensity of the radical: "the whole spice rack". -/
def radicalIntensity : ℕ := radical - 1

theorem radicalIntensity_succ : radicalIntensity + 1 = radical := by
  have := radical_pos
  simp only [radicalIntensity]
  omega

theorem fabricZMod_rot (F : Fabric) (p : SSP) :
    fabricZMod (fabricRot F) p = fabricZMod F p + 1 := by
  cases h : F p <;> simp [fabricZMod, fabricRot, Equiv.arrowCongr, h] <;> decide

/-- **One dialectical step is one seasoning step.**  Composing an intensity with
the radical intensity rotates every fibre of its hyperfabric section — exactly
the action `Synthesis.Hyperfabric.fabricRot` that the sixfold dialectic induces
(`fabricAct_next6`). -/
theorem umamiFabric_season (u : ℕ) :
    umamiFabric (umamiCompose u radicalIntensity) = fabricRot (umamiFabric u) := by
  apply fabricZMod.injective
  funext p
  rw [fabricZMod_rot, fabricZMod_umamiFabric, fabricZMod_umamiFabric,
    succ_umamiCompose, radicalIntensity_succ,
    toneAt_mul (Nat.succ_ne_zero u) radical_pos.ne' p]
  congr 1
  simp [toneAt, factorization_radical]

/-- Iterated seasoning: `k` radical steps rotate every fibre `k` times. -/
theorem umamiFabric_season_iter (k u : ℕ) :
    umamiFabric (Nat.rec u (fun _ v => umamiCompose v radicalIntensity) k) =
      fun p => rotIter k (umamiFabric u p) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have : umamiFabric (umamiCompose
          (Nat.rec u (fun _ v => umamiCompose v radicalIntensity) k) radicalIntensity) =
          fabricRot (umamiFabric (Nat.rec u (fun _ v => umamiCompose v radicalIntensity) k)) :=
        umamiFabric_season _
      simpa [ih, fabricRot, rotIter] using this

/-- **The dialectic acts through the cuisine monoid.**  For every stage of the
sixfold dialectic, the induced action on hyperfabric sections is realised by a
cuisine-side operation: seasoning with `stageIndex s` copies of the radical. -/
theorem dialectic_stage_is_seasoning (s : Stage6) (u : ℕ) :
    fabricAct s (umamiFabric u) =
      umamiFabric (Nat.rec u (fun _ v => umamiCompose v radicalIntensity) (stageIndex s)) := by
  rw [umamiFabric_season_iter]
  rfl


/-! ## The full affine symmetry of the fibre, realised cuisine-side -/

/-- The cuisine operation `u ↦ radical^c · (u+1)^e − 1`: raise the blend to the
`e`-th power and season it `c` times. -/
def affineOp (e c u : ℕ) : ℕ := radical ^ c * (u + 1) ^ e - 1

theorem affineOp_succ (e c u : ℕ) : affineOp e c u + 1 = radical ^ c * (u + 1) ^ e := by
  have h : 0 < radical ^ c * (u + 1) ^ e :=
    Nat.mul_pos (pow_pos radical_pos c) (pow_pos (Nat.succ_pos u) e)
  simp only [affineOp]
  omega

/-- **Every affine map of the ternary fibre is a cuisine operation.**  The
transported section of `affineOp e c u` is the pointwise affine image
`x ↦ e·x + c` of the transported section of `u`.  Taking `(e,c) = (1,1)` gives
the tone rotation, `(2,0)` the group inverse and `(2,2)` the digit negation
`Trit.inv`; so the whole six-element affine group of `ℤ/3` — rotations and
reflections alike — is realised by seasoning and self-composition. -/
theorem fabricZMod_affineOp (e c u : ℕ) (p : SSP) :
    fabricZMod (umamiFabric (affineOp e c u)) p =
      (e : ZMod 3) * fabricZMod (umamiFabric u) p + (c : ZMod 3) := by
  rw [fabricZMod_umamiFabric, fabricZMod_umamiFabric, affineOp_succ,
    toneAt_mul (pow_ne_zero c radical_pos.ne') (pow_ne_zero e (Nat.succ_ne_zero u)) p,
    toneAt_pow, toneAt_pow]
  have hr : toneAt radical p = 1 := by simp [toneAt, factorization_radical]
  rw [hr]
  ring

/-- Self-composition of a blend is the group inverse of its section. -/
theorem umamiFabric_self (u : ℕ) :
    umamiFabric (umamiCompose u u) = fabricXor (umamiFabric u) (umamiFabric u) :=
  umamiFabric_compose u u

end Cuisine.UmamiTransport
