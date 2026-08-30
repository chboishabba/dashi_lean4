import Cuisine.NonaryAction

/-!
# The canonical `3 · 5` grid: the moonshine trivector *is* the umami column

`Cuisine.NineSheet` exhibits the fifteen-element supersingular base in the shape
`3 · 5` through a *chosen* bijection `sspToneTaste`, and `Cuisine.NonaryAction`
then proves the honest negative `base_rotation_moves_moonshine`: the order-three
rotation of that grid carries the Monster trivector `{47, 59, 71}` to
`{19, 23, 29}` and its product from `196883` to `12673`.  The transport report
flagged two consequences as the next obligations — that the `3 · 5` indexing was
an arbitrary choice, and that the two order-three base symmetries in the corpus
(`baseRot` and `moonshineRot`) were unrelated to each other.

This file closes both, and the closure is not a patch: there is a *canonical*
`3 · 5` grid on the supersingular base, and in it the moonshine trivector is one
of the five columns.

## The canonical grid

Order the fifteen supersingular primes and read the ordinal index in base three,
column-major:

```
index p = 3 · (column index) + (tone index)
```

`canonGrid_index` proves exactly this.  The columns are the five consecutive
triples

```
sweet  = {  2,  3,  5 }     product     30
salty  = {  7, 11, 13 }     product   1001
sour   = { 17, 19, 23 }     product   7429
bitter = { 29, 31, 41 }     product  36859
umami  = { 47, 59, 71 }     product 196883 = repDim
```

so the *last* column is the trivector (`trivector_eq_umami_column`,
`blockProduct_umami`) and its product is the supplied moonshine numeral.  Note
which column it is: `umami` is the taste whose interaction law
(`Cuisine.SensoryCore.UmamiBlend.succ_combined_eq`) is what carries the whole
cuisine transport into the Monster base in the first place.  Nothing was tuned
to make that happen; the grid is fixed by the prime order alone.

`canonGrid_is_transpose` records the exact relation to the earlier choice: both
grids are digit readings of the same ordinal index, and they are transposes of
one another — `sspToneTaste` is `5 · tone + taste`, the canonical grid is
`3 · taste + tone`.  Only the latter has consecutive columns, and
`sspToneTaste_column_not_trivector` shows the earlier grid has no column equal to
the trivector at all.

## The symmetry group of the canonical grid

Rotating each column independently gives `blockTwist`, an action of `(ℤ/3)^5` —
order `243` — on the base.  Everything in it is a moonshine symmetry
(`blockTwist_preserves_trivector`, `blockTwist_preserves_repDim`), because every
column is preserved setwise.  The two previously unrelated symmetries both live
in it:

* `blockRot = blockTwist 1`, the diagonal — the canonical grid's own `369`
  rotation, which *does* fix the trivector (`blockRot_preserves_repDim`), in
  contrast with `baseRot`;
* `moonshineRot = blockTwist e_umami`, the `umami` coordinate
  (`moonshineRot_eq_blockTwist`).

Hence `blockRot` and `moonshineRot` commute (`blockRot_comm_moonshineRot`) and
the group they generate is a nonary `ℤ/3 × ℤ/3` inside the `243`
(`two_symmetries_generate_nonary`), which is the frontier question, answered.

Adjoining the `369` rotation of the *fibre*, which commutes with every base
reindexing (`Cuisine.NonaryAction.pullBy_fabricRot`), gives `BlockSymmetry` of
order `3 ^ 6 = 729`, acting faithfully on the hyperfabric
(`blockAct_faithful`).  Against `Fintype.card Fabric = 3 ^ 15` that reads

```
3 ^ 15 = 3 ^ 9 · 3 ^ 6 = 19683 · 729
```

(`card_fabric_eq_nine_sheet_mul_symmetry`), giving the corpus's `19683` a
referent relative to a group that is actually constructed here.  Honest caveat:
that is an identity between two computed cardinalities, not an orbit count — the
action is not free, and no orbit decomposition is claimed.

## Boundary

Nothing here defines the Monster group, a representation of it, or the
`j`-invariant.  `repDim = 196883` and `jCoefficient = 196884` remain supplied
numerals; what is proved is that the canonical grid puts them on a column, and
that the column rotations fix them.
-/

namespace Cuisine.CanonicalGrid

open AgdaMirror.DASHIAlgebra (Trit)
open AgdaMirror.Base369 (TriTruth rotateTri)
open AgdaMirror.TritBridge (rotTrit)
open AgdaMirror.MonsterOntos (SSP)
open Synthesis.MonsterFibre
open Synthesis.Hyperfabric
open Synthesis.MoonshineBase
open Cuisine.SensoryCore (TasteDimension)
open Cuisine.NineSheet (sspToneTaste)
open Cuisine.NonaryAction (pullBy moonshineRot)

/-! ## The canonical grid -/

/-- The column of a supersingular prime: the five consecutive triples of the
ordered base, named by the cuisine taste dimensions. -/
def blockOf : SSP → TasteDimension
  | .p2 | .p3 | .p5 => .sweet
  | .p7 | .p11 | .p13 => .salty
  | .p17 | .p19 | .p23 => .sour
  | .p29 | .p31 | .p41 => .bitter
  | .p47 | .p59 | .p71 => .umami

/-- The tone of a supersingular prime: its position inside its column. -/
def toneOf : SSP → TriTruth
  | .p2 | .p7 | .p17 | .p29 | .p47 => .low
  | .p3 | .p11 | .p19 | .p31 | .p59 => .mid
  | .p5 | .p13 | .p23 | .p41 | .p71 => .high

/-- The least prime of a column. -/
def blockLow : TasteDimension → SSP
  | .sweet => .p2 | .salty => .p7 | .sour => .p17 | .bitter => .p29 | .umami => .p47

/-- The canonical `3 · 5` grid on the supersingular base. -/
def canonGrid : SSP ≃ TriTruth × TasteDimension where
  toFun p := (toneOf p, blockOf p)
  invFun
    | (.low, .sweet) => .p2 | (.mid, .sweet) => .p3 | (.high, .sweet) => .p5
    | (.low, .salty) => .p7 | (.mid, .salty) => .p11 | (.high, .salty) => .p13
    | (.low, .sour) => .p17 | (.mid, .sour) => .p19 | (.high, .sour) => .p23
    | (.low, .bitter) => .p29 | (.mid, .bitter) => .p31 | (.high, .bitter) => .p41
    | (.low, .umami) => .p47 | (.mid, .umami) => .p59 | (.high, .umami) => .p71
  left_inv := by decide
  right_inv := by decide

/-- Index of a taste dimension in the prime order. -/
def tasteIndex : TasteDimension → Nat
  | .sweet => 0 | .salty => 1 | .sour => 2 | .bitter => 3 | .umami => 4

/-- Index of a tone. -/
def toneIndex : TriTruth → Nat
  | .low => 0 | .mid => 1 | .high => 2

/-- **The canonical grid is the base-three reading of the prime order.**  The
ordinal index of a supersingular prime is `3 · (column) + (tone)`; no choice is
involved beyond ordering the primes. -/
theorem canonGrid_index (p : SSP) :
    (sspToFin p : Nat) = 3 * tasteIndex (blockOf p) + toneIndex (toneOf p) := by
  cases p <;> rfl

/-- The chosen grid of `Cuisine.NineSheet` is the *other* digit reading of the
same index, `5 · (tone) + (taste)`; the two grids are transposes. -/
theorem sspToneTaste_index (p : SSP) :
    (sspToFin p : Nat) =
      5 * toneIndex (sspToneTaste p).1 + tasteIndex (sspToneTaste p).2 := by
  cases p <;> rfl

/-- Stated together: both `3 · 5` grids on the base are digit readings of the
ordinal index, and they differ by transposing the radix order. -/
theorem canonGrid_is_transpose (p : SSP) :
    3 * tasteIndex (canonGrid p).2 + toneIndex (canonGrid p).1 =
      5 * toneIndex (sspToneTaste p).1 + tasteIndex (sspToneTaste p).2 :=
  (canonGrid_index p).symm.trans (sspToneTaste_index p)

/-- The two grids are genuinely different bijections. -/
theorem canonGrid_ne_sspToneTaste :
    ∃ p : SSP, canonGrid p ≠ sspToneTaste p :=
  ⟨SSP.p3, by decide⟩

/-! ## The columns -/

/-- The mask selecting a column. -/
def blockMask (d : TasteDimension) : MaskSSP := fun p => decide (blockOf p = d)

/-- The product of the primes in a column. -/
def blockProduct (d : TasteDimension) : Nat := maskProduct (blockMask d)

theorem blockProduct_values :
    blockProduct .sweet = 30 ∧ blockProduct .salty = 1001 ∧
      blockProduct .sour = 7429 ∧ blockProduct .bitter = 36859 ∧
      blockProduct .umami = 196883 :=
  ⟨by decide, by decide, by decide, by decide, by decide⟩

/-- **The moonshine trivector is exactly the `umami` column of the canonical
grid.** -/
theorem trivector_eq_umami_column : blockMask .umami = trivectorMask := by decide

/-- ... so the supplied moonshine numeral is the product of one column. -/
theorem blockProduct_umami : blockProduct .umami = AgdaMirror.Moonshine.repDim := by decide

/-- ... and adding the supplied observer `+1` gives `jCoefficient`. -/
theorem blockProduct_umami_succ :
    blockProduct .umami + 1 = AgdaMirror.Moonshine.jCoefficient := by decide

/-- The five column products multiply to the product of the whole base. -/
theorem prod_blockProduct :
    blockProduct .sweet * blockProduct .salty * blockProduct .sour *
        blockProduct .bitter * blockProduct .umami = maskProduct fullMaskSSP := by
  rw [maskProduct_full]
  have h := blockProduct_values
  rw [h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2]

/-- The earlier, non-canonical grid has no column equal to the trivector: the
repair really needed the change of grid, not a change of permutation. -/
theorem sspToneTaste_column_not_trivector (d : TasteDimension) :
    (fun p => decide ((sspToneTaste p).2 = d)) ≠ trivectorMask := by
  cases d <;> decide

theorem blockOf_blockLow (d : TasteDimension) : blockOf (blockLow d) = d := by cases d <;> rfl

/-! ## The column rotations -/

/-- The canonical base rotation: advance inside each column. -/
def blockRot : SSP → SSP
  | .p2 => .p3 | .p3 => .p5 | .p5 => .p2
  | .p7 => .p11 | .p11 => .p13 | .p13 => .p7
  | .p17 => .p19 | .p19 => .p23 | .p23 => .p17
  | .p29 => .p31 | .p31 => .p41 | .p41 => .p29
  | .p47 => .p59 | .p59 => .p71 | .p71 => .p47

/-- `blockRot` is the tone rotation read through the canonical grid. -/
theorem blockRot_eq_grid (p : SSP) :
    blockRot p = canonGrid.symm (rotateTri (canonGrid p).1, (canonGrid p).2) := by
  cases p <;> rfl

theorem blockRot_cube (p : SSP) : blockRot (blockRot (blockRot p)) = p := by cases p <;> rfl

theorem blockRot_no_fixpoint (p : SSP) : blockRot p ≠ p := by cases p <;> decide

theorem blockRot_injective : Function.Injective blockRot := by decide

theorem blockOf_blockRot (p : SSP) : blockOf (blockRot p) = blockOf p := by cases p <;> rfl

/-- **The canonical base rotation preserves the trivector**, in contrast with
`Cuisine.NonaryAction.base_rotation_moves_moonshine`. -/
theorem blockRot_preserves_trivector (p : SSP) :
    trivectorMask (blockRot p) = trivectorMask p := by cases p <;> rfl

theorem blockRot_preserves_repDim :
    maskProduct (fun p => trivectorMask (blockRot p)) = AgdaMirror.Moonshine.repDim := by
  have h : (fun p => trivectorMask (blockRot p)) = trivectorMask := by
    funext p; exact blockRot_preserves_trivector p
  rw [h]; exact maskProduct_trivector

/-- Iterated column rotation. -/
def blockRotIter : Nat → SSP → SSP
  | 0, p => p
  | n + 1, p => blockRot (blockRotIter n p)

theorem blockRotIter_add (m n : Nat) (p : SSP) :
    blockRotIter (m + n) p = blockRotIter m (blockRotIter n p) := by
  induction m with
  | zero => rw [Nat.zero_add]; rfl
  | succ k ih =>
      rw [Nat.succ_add]
      show blockRot (blockRotIter (k + n) p) = blockRot (blockRotIter k (blockRotIter n p))
      rw [ih]

theorem blockOf_blockRotIter (n : Nat) (p : SSP) : blockOf (blockRotIter n p) = blockOf p := by
  induction n with
  | zero => rfl
  | succ k ih => show blockOf (blockRot (blockRotIter k p)) = _; rw [blockOf_blockRot, ih]

theorem blockRotIter_three_mul (k : Nat) (p : SSP) : blockRotIter (3 * k) p = p := by
  induction k with
  | zero => rfl
  | succ m ih =>
      have h : 3 * (m + 1) = 3 + 3 * m := by ring
      rw [h, blockRotIter_add, ih]
      exact blockRot_cube p

theorem blockRotIter_mod (n : Nat) (p : SSP) : blockRotIter n p = blockRotIter (n % 3) p := by
  conv_lhs => rw [← Nat.div_add_mod n 3]
  rw [blockRotIter_add, blockRotIter_three_mul]

theorem blockRotIter_inj_aux :
    ∀ (p : SSP) (a b : Fin 3), blockRotIter a.val p = blockRotIter b.val p → a = b := by decide

theorem blockRotIter_inj {a b : Fin 3} {p : SSP}
    (h : blockRotIter a.val p = blockRotIter b.val p) : a = b :=
  blockRotIter_inj_aux p a b h

/-! ## The group of column twists -/

/-- Rotate each column independently: an action of `(ℤ/3) ^ 5` on the base. -/
def blockTwist (v : TasteDimension → Fin 3) : SSP → SSP :=
  fun p => blockRotIter (v (blockOf p)).val p

theorem blockOf_blockTwist (v : TasteDimension → Fin 3) (p : SSP) :
    blockOf (blockTwist v p) = blockOf p := blockOf_blockRotIter _ p

/-- **The column twists compose additively**: `blockTwist` is a homomorphism from
`(ℤ/3) ^ 5`. -/
theorem blockTwist_comp (v w : TasteDimension → Fin 3) (p : SSP) :
    blockTwist v (blockTwist w p) = blockTwist (v + w) p := by
  show blockRotIter (v (blockOf (blockTwist w p))).val (blockRotIter (w (blockOf p)).val p) = _
  rw [blockOf_blockTwist, ← blockRotIter_add]
  show _ = blockRotIter ((v (blockOf p) + w (blockOf p) : Fin 3)).val p
  rw [Fin.val_add]
  exact blockRotIter_mod _ p

theorem blockTwist_zero (p : SSP) : blockTwist 0 p = p := by
  show blockRotIter ((0 : Fin 3)).val p = p
  rfl

/-- **Every column twist is a moonshine symmetry**: columns are preserved
setwise, so the `umami` column — the trivector — is too. -/
theorem blockTwist_preserves_trivector (v : TasteDimension → Fin 3) (p : SSP) :
    trivectorMask (blockTwist v p) = trivectorMask p := by
  rw [← trivector_eq_umami_column]
  simp only [blockMask, blockOf_blockTwist]

theorem blockTwist_preserves_repDim (v : TasteDimension → Fin 3) :
    maskProduct (fun p => trivectorMask (blockTwist v p)) = AgdaMirror.Moonshine.repDim := by
  have h : (fun p => trivectorMask (blockTwist v p)) = trivectorMask := by
    funext p; exact blockTwist_preserves_trivector v p
  rw [h]; exact maskProduct_trivector

/-- **The twist group acts faithfully on the base**, so it really has `243`
elements. -/
theorem blockTwist_faithful {v w : TasteDimension → Fin 3}
    (h : blockTwist v = blockTwist w) : v = w := by
  funext d
  have hd := congrFun h (blockLow d)
  rw [blockTwist, blockTwist, blockOf_blockLow] at hd
  exact blockRotIter_inj hd

theorem card_twist_group : Fintype.card (TasteDimension → Fin 3) = 243 := by
  rw [Fintype.card_fun]
  decide

/-! ## The two order-three symmetries, reconciled -/

/-- The all-ones twist. -/
def oneTwist : TasteDimension → Fin 3 := fun _ => 1

/-- The `umami` coordinate twist. -/
def umamiTwist : TasteDimension → Fin 3 := fun d => if d = .umami then 1 else 0

/-- The canonical base rotation is the diagonal of the twist group. -/
theorem blockRot_eq_blockTwist : blockTwist oneTwist = blockRot := by
  funext p; cases p <;> rfl

/-- **The trivector three-cycle of `Cuisine.NonaryAction` is the `umami`
coordinate of the twist group.**  The two order-three base symmetries in the
corpus are two elements of one abelian group. -/
theorem moonshineRot_eq_blockTwist : blockTwist umamiTwist = moonshineRot := by
  funext p; cases p <;> rfl

theorem blockRot_comm_moonshineRot (p : SSP) :
    blockRot (moonshineRot p) = moonshineRot (blockRot p) := by cases p <;> rfl

/-- **The frontier question, answered.**  The two order-three base symmetries
commute, each has order three, every product of them is a column twist, and the
nine products are pairwise distinct: the group they generate is a nonary
`ℤ/3 × ℤ/3` inside the `243`-element column-twist group, every element of which
fixes the trivector. -/
theorem two_symmetries_generate_nonary :
    (∀ p, blockRot (moonshineRot p) = moonshineRot (blockRot p)) ∧
      (∀ p, blockRot (blockRot (blockRot p)) = p) ∧
      (∀ p, moonshineRot (moonshineRot (moonshineRot p)) = p) ∧
      (∀ i j : Fin 3,
        (fun p => blockRotIter i.val (moonshineRot^[j.val] p)) =
          blockTwist (fun d => if d = .umami then i + j else i)) ∧
      (∀ i j i' j' : Fin 3,
        (fun p => blockRotIter i.val (moonshineRot^[j.val] p)) =
            (fun p => blockRotIter i'.val (moonshineRot^[j'.val] p)) →
          i = i' ∧ j = j') :=
  ⟨blockRot_comm_moonshineRot, blockRot_cube, Cuisine.NonaryAction.moonshineRot_cube,
    by decide, by decide⟩

/-! ## The full commuting symmetry of the hyperfabric -/

/-- The symmetry group of the canonical grid together with the `369` rotation of
the fibre: `(ℤ/3) ^ 5 × ℤ/3`. -/
abbrev BlockSymmetry := (TasteDimension → Fin 3) × Fin 3

/-- Its action on the hyperfabric: twist the base, rotate the fibre. -/
def blockAct (g : BlockSymmetry) (F : Fabric) : Fabric :=
  fun p => rotIter g.2.val (F (blockTwist g.1 p))

theorem card_blockSymmetry : Fintype.card BlockSymmetry = 3 ^ 6 := by
  rw [Fintype.card_prod, Fintype.card_fun]
  decide

theorem card_blockSymmetry_val : Fintype.card BlockSymmetry = 729 := by
  rw [card_blockSymmetry]; norm_num

/-- Base twisting and fibre rotation are the two independent halves of the
action. -/
theorem blockAct_split (g : BlockSymmetry) (F : Fabric) :
    blockAct g F = pullBy (blockTwist g.1) (fun p => rotIter g.2.val (F p)) := rfl

theorem rotIter_rotTrit (n : Nat) (t : Trit) :
    rotIter n (rotTrit t) = rotTrit (rotIter n t) := by
  induction n with
  | zero => rfl
  | succ k ih => exact congrArg rotTrit ih

/-- **The whole symmetry commutes with the `369` rotation of the fibre.** -/
theorem blockAct_comm_fabricRot (g : BlockSymmetry) (F : Fabric) :
    blockAct g (fabricRot F) = fabricRot (blockAct g F) := by
  funext p
  exact rotIter_rotTrit g.2.val (F (blockTwist g.1 p))

theorem rotTrit_injective : Function.Injective rotTrit := by decide

theorem rotIter_injective (n : Nat) : Function.Injective (rotIter n) := by
  induction n with
  | zero => exact fun _ _ h => h
  | succ k ih => exact fun _ _ h => ih (rotTrit_injective h)

/-- A section that is `pos` at exactly one base point. -/
def point (q : SSP) : Fabric := fun r => if r = q then Trit.pos else Trit.neg

/-- **The order-`729` symmetry acts faithfully on the hyperfabric.** -/
theorem blockAct_faithful {g g' : BlockSymmetry} (h : blockAct g = blockAct g') : g = g' := by
  have hfib : ∀ a b : Fin 3, rotIter a.val Trit.neg = rotIter b.val Trit.neg → a = b := by decide
  have h2 : g.2 = g'.2 := by
    refine hfib g.2 g'.2 ?_
    exact congrFun (congrFun h (fun _ => Trit.neg)) SSP.p2
  refine Prod.ext ?_ h2
  refine blockTwist_faithful ?_
  funext p
  by_contra hne
  have key : rotIter g.2.val (point (blockTwist g.1 p) (blockTwist g.1 p)) =
      rotIter g'.2.val (point (blockTwist g.1 p) (blockTwist g'.1 p)) :=
    congrFun (congrFun h (point (blockTwist g.1 p))) p
  have e1 : point (blockTwist g.1 p) (blockTwist g.1 p) = Trit.pos := by simp [point]
  have e2 : point (blockTwist g.1 p) (blockTwist g'.1 p) = Trit.neg := by
    simp [point, Ne.symm hne]
  rw [e1, e2, h2] at key
  exact absurd (rotIter_injective g'.2.val key) (by decide)

/-- **`3 ^ 15 = 19683 · 729`**: the number of hyperfabric sections is `3 ^ 9`
times the order of the commuting symmetry group constructed above.  This is an
identity between two computed cardinalities, not an orbit count. -/
theorem card_fabric_eq_nine_sheet_mul_symmetry :
    Fintype.card Fabric = 3 ^ 9 * Fintype.card BlockSymmetry := by
  rw [card_fabric, card_blockSymmetry]; norm_num

theorem card_fabric_nineteen_thousand : Fintype.card Fabric = 19683 * 729 := by
  rw [card_fabric_eq_nine_sheet_mul_symmetry, card_blockSymmetry_val]; norm_num

/-! ## Cuisine side -/

/-- The whole `729`-element symmetry is realised on cuisine data: the image of a
blend under it is again the transport of a blend. -/
theorem exists_blockAct_intensity (g : BlockSymmetry) (u : Nat) :
    ∃ v : Nat, blockAct g (Cuisine.UmamiTransport.umamiFabric u) =
      Cuisine.UmamiTransport.umamiFabric v :=
  ⟨Cuisine.UmamiTransport.fabricIntensity _,
    (Cuisine.UmamiTransport.umamiFabric_fabricIntensity _).symm⟩

/-- **The headline.**  In the canonical grid the Monster trivector is the umami
column, its product is the supplied `repDim`, the column rotation fixes it, and
so does the whole `243`-element column group. -/
theorem moonshine_is_the_umami_column :
    blockMask .umami = trivectorMask ∧
      blockProduct .umami = AgdaMirror.Moonshine.repDim ∧
      (∀ p, trivectorMask (blockRot p) = trivectorMask p) ∧
      (∀ (v : TasteDimension → Fin 3) p, trivectorMask (blockTwist v p) = trivectorMask p) :=
  ⟨trivector_eq_umami_column, blockProduct_umami, blockRot_preserves_trivector,
    blockTwist_preserves_trivector⟩

end Cuisine.CanonicalGrid
