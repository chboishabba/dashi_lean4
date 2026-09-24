import Cuisine.NineSheet

/-!
# The nonary action: base rotation and fibre rotation on the hyperfabric

`Cuisine.NineSheet` exhibits the fifteen-element Monster prime base in the shape
`3 · 5` — three tones times five cuisine taste dimensions — and shows the two
readings of a section commute (`grid_flip`).  That factorisation gives the base
its own order-three rotation, *independent of* the tone rotation already acting
on the fibre.  This file makes both actions explicit and puts them together.

* `baseRot` — the tone rotation of the base: `p ↦` the next prime in the same
  taste column.  Order three (`baseRot_cube`) and fixed-point free
  (`baseRot_no_fixpoint`).
* `fabricPull` — reindexing a section along `baseRot`.
* `fabricPull_fabricRot` — **the two rotations commute**, so the hyperfabric
  carries an action of `ℤ/3 × ℤ/3`: the nonary group.  `nonaryAct` packages it,
  `nonary_period` gives the orders, and `nonary_faithful` proves the nine
  operators are pairwise distinct — the action really is nonary, not ternary in
  disguise.  This is the honest referent of the corpus's
  "Tlurey triadic/nonary" motif: a nine-element group acting on the ternary
  hyperfabric, built from the `3 · 5` shape of the Monster prime base and the
  `369` rotation of the fibre.
* `baseInvariantEquiv`, `card_baseInvariant` — the sections fixed by the base
  rotation are exactly the taste-indexed ones, and there are `3 ^ 5 = 243` of
  them; combined with `Cuisine.NineSheet.card_fabric_grid` this is the
  `3 ^ 15 = (3 ^ 5) ^ 3` factorisation realised as an orbit count.
* `no_rot_invariant` — by contrast the *fibre* rotation fixes no section at all.
* `moonshineRot`, `moonshine_preserving_symmetry` — the repair: the three-cycle
  of the trivector primes `47 → 59 → 71 → 47` *is* an order-three base symmetry
  that commutes with the fibre rotation and fixes the trivector mask and its
  product `196883`.  Its invariant sections number `3 ^ 13 = 1594323`
  (`card_moonshineInvariant`), and its joint action with the fibre rotation is
  again faithfully nonary (`moonshine_nonary_faithful`).  Honest caveat: unlike
  `baseRot` it has twelve fixed points (`moonshineRot_fixes_small`).
* `maskPull_trivector`, `base_rotation_moves_moonshine` — the honest negative:
  the base rotation does **not** preserve the moonshine trivector mask.  It
  carries `{47, 59, 71}` to `{19, 23, 29}` and the mask product from `196883`
  to `12673`, so the `369` rotation of the base is not a symmetry of the
  moonshine data.  Any claim that it is would be false, and this theorem says
  so.

Boundary: `baseRot` depends on the chosen bijection `sspToneTaste`, which
`Cuisine.NineSheet` already flags as a choice.  Everything below is a statement
about that chosen grid; nothing here is a statement about the Monster group.
-/

namespace Cuisine.NonaryAction

open AgdaMirror.DASHIAlgebra (Trit)
open AgdaMirror.Base369 (TriTruth rotateTri)
open AgdaMirror.TritBridge (rotTrit)
open AgdaMirror.MonsterOntos (SSP)
open Synthesis.MonsterFibre
open Synthesis.Hyperfabric
open Synthesis.MoonshineBase
open Cuisine.SensoryCore (TasteDimension)
open Cuisine.UmamiTransport
open Cuisine.NineSheet

/-! ## The rotation of the base -/

/-- The tone rotation of the base: advance the tone coordinate of the `3 · 5`
grid, keeping the taste coordinate fixed. -/
def baseRot : SSP → SSP
  | .p2 => .p13 | .p13 => .p31 | .p31 => .p2
  | .p3 => .p17 | .p17 => .p41 | .p41 => .p3
  | .p5 => .p19 | .p19 => .p47 | .p47 => .p5
  | .p7 => .p23 | .p23 => .p59 | .p59 => .p7
  | .p11 => .p29 | .p29 => .p71 | .p71 => .p11

/-- `baseRot` is exactly the tone rotation read through the chosen grid. -/
theorem baseRot_eq_grid (p : SSP) :
    baseRot p = sspToneTaste.symm (rotateTri (sspToneTaste p).1, (sspToneTaste p).2) := by
  cases p <;> rfl

theorem baseRot_cube (p : SSP) : baseRot (baseRot (baseRot p)) = p := by cases p <;> rfl

theorem baseRot_no_fixpoint (p : SSP) : baseRot p ≠ p := by cases p <;> decide

theorem baseRot_injective : Function.Injective baseRot := by decide

/-- Iterated base rotation. -/
def baseRotIter : Nat → SSP → SSP
  | 0, p => p
  | n + 1, p => baseRot (baseRotIter n p)

theorem baseRotIter_three (p : SSP) : baseRotIter 3 p = p := baseRot_cube p

/-! ## The taste column of a base point -/

/-- The taste column a base point lies in. -/
def tasteOf : SSP → TasteDimension
  | .p2 | .p13 | .p31 => .sweet
  | .p3 | .p17 | .p41 => .salty
  | .p5 | .p19 | .p47 => .sour
  | .p7 | .p23 | .p59 => .bitter
  | .p11 | .p29 | .p71 => .umami

/-- The base point at the bottom of a taste column. -/
def tasteBase : TasteDimension → SSP
  | .sweet => .p2 | .salty => .p3 | .sour => .p5 | .bitter => .p7 | .umami => .p11

theorem tasteOf_baseRot (p : SSP) : tasteOf (baseRot p) = tasteOf p := by cases p <;> rfl

theorem tasteOf_tasteBase (d : TasteDimension) : tasteOf (tasteBase d) = d := by
  cases d <;> rfl

theorem tasteOf_eq_grid (p : SSP) : tasteOf p = (sspToneTaste p).2 := by cases p <;> rfl

/-! ## The two rotations of the hyperfabric -/

/-- Reindex a section along the base rotation. -/
def fabricPull (F : Fabric) : Fabric := fun p => F (baseRot p)

theorem fabricPull_cube (F : Fabric) : fabricPull (fabricPull (fabricPull F)) = F := by
  funext p
  simp only [fabricPull]
  rw [baseRot_cube]

/-- **The base rotation and the fibre rotation commute.** -/
theorem fabricPull_fabricRot (F : Fabric) :
    fabricPull (fabricRot F) = fabricRot (fabricPull F) := rfl

/-- The joint action of the nonary group: rotate the fibre `i` times and the
base `j` times. -/
def nonaryAct (i j : Nat) (F : Fabric) : Fabric := fun p => rotIter i (F (baseRotIter j p))

@[simp] theorem nonaryAct_zero (F : Fabric) : nonaryAct 0 0 F = F := rfl

theorem nonaryAct_fibre (F : Fabric) : nonaryAct 1 0 F = fabricRot F := rfl

theorem nonaryAct_base (F : Fabric) : nonaryAct 0 1 F = fabricPull F := rfl

/-- **The two generators commute and each has order three**, so the action is an
action of `ℤ/3 × ℤ/3`. -/
theorem nonary_period (F : Fabric) :
    nonaryAct 3 0 F = F ∧ nonaryAct 0 3 F = F ∧
      nonaryAct 1 1 F = fabricRot (fabricPull F) ∧
      fabricRot (fabricPull F) = fabricPull (fabricRot F) := by
  refine ⟨?_, ?_, rfl, rfl⟩
  · funext p; exact rotIter_three _
  · funext p; simp only [nonaryAct, rotIter]; rw [baseRotIter_three]

/-- A section that separates the nine operators. -/
def probe : Fabric
  | .p2 => .zer
  | .p13 => .pos
  | _ => .neg

/-- **The action is faithful**: the nine operators are pairwise distinct on the
single section `probe`, so `ℤ/3 × ℤ/3` acts without kernel. -/
theorem nonary_faithful_probe (i j i' j' : Fin 3)
    (h : nonaryAct i j probe = nonaryAct i' j' probe) : i = i' ∧ j = j' := by
  revert h; revert i j i' j'; decide

theorem nonary_faithful (i j i' j' : Fin 3)
    (h : nonaryAct i j = nonaryAct i' j') : i = i' ∧ j = j' :=
  nonary_faithful_probe i j i' j' (congrFun h probe)

/-- The nonary group has nine elements: this is the `nonary` carrier the corpus
names, realised as a group acting on the hyperfabric. -/
theorem card_nonary : Fintype.card (Fin 3 × Fin 3) = 9 := rfl

/-! ## Invariants -/

instance : DecidableEq Fabric := inferInstance

/-- The sections fixed by the base rotation. -/
def BaseInvariant : Type := {F : Fabric // fabricPull F = F}

instance : Fintype BaseInvariant := by unfold BaseInvariant; infer_instance

/-- **A base-invariant section is exactly a taste-indexed one.**  Invariance
under the `369` rotation of the base collapses the fifteen-point base onto its
five taste columns. -/
def baseInvariantEquiv : BaseInvariant ≃ (TasteDimension → Trit) where
  toFun F := fun d => F.val (tasteBase d)
  invFun g := ⟨fun p => g (tasteOf p), by funext p; cases p <;> rfl⟩
  left_inv := by
    rintro ⟨F, hF⟩
    apply Subtype.ext
    funext p
    have h : ∀ q, F (baseRot q) = F q := fun q => congrFun hF q
    have h2 : ∀ q, F (baseRot (baseRot q)) = F q := fun q => (h (baseRot q)).trans (h q)
    show F (tasteBase (tasteOf p)) = F p
    cases p
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact h2 SSP.p13
    · exact h2 SSP.p17
    · exact h2 SSP.p19
    · exact h2 SSP.p23
    · exact h2 SSP.p29
    · exact h SSP.p31
    · exact h SSP.p41
    · exact h SSP.p47
    · exact h SSP.p59
    · exact h SSP.p71
  right_inv g := by funext d; cases d <;> rfl

/-- **`3 ^ 5 = 243` sections are base-invariant.**  With
`Cuisine.NineSheet.card_fabric_grid` (`3 ^ 15 = (3 ^ 5) ^ 3`) this exhibits the
grid factorisation as the invariant count of the base rotation. -/
theorem card_baseInvariant : Fintype.card BaseInvariant = 243 := by
  rw [Fintype.card_congr baseInvariantEquiv, Fintype.card_fun]
  rfl

/-- **The fibre rotation fixes nothing.**  Unlike the base rotation, the `369`
rotation of the fibre has no invariant section whatsoever. -/
theorem no_rot_invariant (F : Fabric) : fabricRot F ≠ F := by
  intro h
  have hno : ∀ t : Trit, rotTrit t ≠ t := by decide
  exact hno (F SSP.p2) (congrFun h SSP.p2)

/-! ## The base rotation against the moonshine data -/

/-- Reindex a Monster mask along the base rotation. -/
def maskPull (m : MaskSSP) : MaskSSP := fun p => m (baseRot p)

theorem supportMask_fabricPull (F : Fabric) :
    supportMask (fabricPull F) = maskPull (supportMask F) := rfl

/-- The base rotation carries the trivector mask `{47, 59, 71}` to
`{19, 23, 29}`. -/
theorem maskPull_trivector (p : SSP) :
    maskPull trivectorMask p = decide (p = .p19 ∨ p = .p23 ∨ p = .p29) := by
  cases p <;> rfl

/-- **The `369` base rotation is not a symmetry of the moonshine data.**  The
mask product drops from `196883 = 47 · 59 · 71` to `12673 = 19 · 23 · 29`, so no
statement identifying the base rotation with a moonshine symmetry can be
true. -/
theorem base_rotation_moves_moonshine :
    maskProduct trivectorMask = AgdaMirror.Moonshine.repDim ∧
      maskProduct (maskPull trivectorMask) = 12673 ∧
      maskProduct (maskPull trivectorMask) ≠ maskProduct trivectorMask := by
  refine ⟨maskProduct_trivector, by decide, by decide⟩

/-! ## Cuisine side -/

/-- The base rotation is realised on the cuisine side: reindexing the transport
of a blend is again the transport of a blend. -/
theorem exists_pull_intensity (u : Nat) : ∃ v : Nat, fabricPull (umamiFabric u) = umamiFabric v :=
  ⟨fabricIntensity (fabricPull (umamiFabric u)), (umamiFabric_fabricIntensity _).symm⟩

/-- Likewise for the whole nonary action. -/
theorem exists_nonary_intensity (i j u : Nat) :
    ∃ v : Nat, nonaryAct i j (umamiFabric u) = umamiFabric v :=
  ⟨fabricIntensity (nonaryAct i j (umamiFabric u)), (umamiFabric_fabricIntensity _).symm⟩

/-! ## A base rotation that *does* preserve the moonshine data

The base rotation above moves the trivector mask, so it is not a moonshine
symmetry.  The obvious repair is to rotate the three trivector primes among
themselves and leave the other twelve alone.  That permutation is again of order
three, again commutes with the `369` rotation of the fibre — every base
permutation does — and it fixes the trivector mask on the nose. -/

/-- Reindex a section along an arbitrary permutation of the base. -/
def pullBy (sigma : SSP → SSP) (F : Fabric) : Fabric := fun p => F (sigma p)

/-- **Any base reindexing commutes with the fibre rotation.** -/
theorem pullBy_fabricRot (sigma : SSP → SSP) (F : Fabric) :
    pullBy sigma (fabricRot F) = fabricRot (pullBy sigma F) := rfl

theorem pullBy_baseRot (F : Fabric) : pullBy baseRot F = fabricPull F := rfl

/-- The three-cycle `47 → 59 → 71 → 47` of the trivector primes. -/
def moonshineRot : SSP → SSP
  | .p47 => .p59 | .p59 => .p71 | .p71 => .p47
  | p => p

theorem moonshineRot_cube (p : SSP) :
    moonshineRot (moonshineRot (moonshineRot p)) = p := by cases p <;> rfl

/-- Honest caveat: unlike `baseRot`, this permutation has fixed points — the
twelve primes below `47`. -/
theorem moonshineRot_fixes_small (p : SSP) :
    moonshineRot p = p ↔ AgdaMirror.MonsterOntos.toNat p < 47 := by
  cases p <;> decide

/-- **The trivector mask is invariant.** -/
theorem moonshineRot_preserves_trivector (p : SSP) :
    trivectorMask (moonshineRot p) = trivectorMask p := by cases p <;> rfl

/-- **A moonshine-preserving symmetry exists.**  Reindexing along `moonshineRot`
commutes with the `369` fibre rotation, has order three, and leaves both the
Monster trivector mask and its product `196883` exactly where they were — in
contrast with `base_rotation_moves_moonshine`. -/
theorem moonshine_preserving_symmetry :
    (∀ F : Fabric, pullBy moonshineRot (fabricRot F) = fabricRot (pullBy moonshineRot F)) ∧
      (∀ F : Fabric,
        pullBy moonshineRot (pullBy moonshineRot (pullBy moonshineRot F)) = F) ∧
      (fun p => trivectorMask (moonshineRot p)) = trivectorMask ∧
      maskProduct (fun p => trivectorMask (moonshineRot p)) = AgdaMirror.Moonshine.repDim := by
  refine ⟨fun F => rfl, ?_, ?_, ?_⟩
  · intro F
    funext p
    simp only [pullBy]
    rw [moonshineRot_cube]
  · funext p; exact moonshineRot_preserves_trivector p
  · exact maskProduct_trivector

/-! ### Its invariants -/

/-- Orbit representatives of `moonshineRot`: every prime but `59` and `71`. -/
def moonshineRep : SSP → SSP
  | .p59 => .p47 | .p71 => .p47
  | p => p

theorem moonshineRep_idem (p : SSP) : moonshineRep (moonshineRep p) = moonshineRep p := by
  cases p <;> rfl

theorem moonshineRep_moonshineRot (p : SSP) :
    moonshineRep (moonshineRot p) = moonshineRep p := by cases p <;> rfl

/-- The thirteen orbits of `moonshineRot`. -/
def MoonshineReps : Type := {p : SSP // moonshineRep p = p}

instance : DecidableEq MoonshineReps := by unfold MoonshineReps; infer_instance

instance : Fintype MoonshineReps := by unfold MoonshineReps; infer_instance

theorem card_moonshineReps : Fintype.card MoonshineReps = 13 := by decide

/-- The sections fixed by the trivector three-cycle. -/
def MoonshineInvariant : Type := {F : Fabric // pullBy moonshineRot F = F}

instance : Fintype MoonshineInvariant := by unfold MoonshineInvariant; infer_instance

/-- A section invariant under the trivector three-cycle is exactly a labelling of
the thirteen orbits. -/
def moonshineInvariantEquiv : MoonshineInvariant ≃ (MoonshineReps → Trit) where
  toFun F := fun q => F.val q.val
  invFun g :=
    ⟨fun p => g ⟨moonshineRep p, moonshineRep_idem p⟩, by funext p; cases p <;> rfl⟩
  left_inv := by
    rintro ⟨F, hF⟩
    apply Subtype.ext
    funext p
    have h : ∀ q, F (moonshineRot q) = F q := fun q => congrFun hF q
    show F (moonshineRep p) = F p
    cases p <;>
      first
        | rfl
        | exact (h SSP.p47).symm
        | exact (h SSP.p47).symm.trans (h SSP.p59).symm
  right_inv g := by
    funext q
    exact congrArg g (Subtype.ext q.property)

/-- **`3 ^ 13 = 1594323` sections are invariant** under the moonshine-preserving
three-cycle: twelve free primes plus one collapsed orbit. -/
theorem card_moonshineInvariant : Fintype.card MoonshineInvariant = 1594323 := by
  rw [Fintype.card_congr moonshineInvariantEquiv, Fintype.card_fun, card_moonshineReps]
  rfl

/-- The joint action of the fibre rotation and the trivector three-cycle. -/
def moonshineNonaryAct (i j : Nat) (F : Fabric) : Fabric :=
  fun p => rotIter i (F (moonshineRot^[j] p))

/-- A section separating the nine operators of that action. -/
def moonshineProbe : Fabric
  | .p47 => .zer
  | .p59 => .pos
  | _ => .neg

/-- **The moonshine-preserving nonary action is faithful too.** -/
theorem moonshine_nonary_faithful_probe (i j i' j' : Fin 3)
    (h : moonshineNonaryAct i j moonshineProbe = moonshineNonaryAct i' j' moonshineProbe) :
    i = i' ∧ j = j' := by
  revert h; revert i j i' j'; decide

theorem moonshine_nonary_faithful (i j i' j' : Fin 3)
    (h : moonshineNonaryAct i j = moonshineNonaryAct i' j') : i = i' ∧ j = j' :=
  moonshine_nonary_faithful_probe i j i' j' (congrFun h moonshineProbe)

end Cuisine.NonaryAction
