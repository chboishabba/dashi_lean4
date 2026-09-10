/-
# The signed-bond transport calculus underlying Bałaban's one-step averaging
derivative (CMP 98, around Eq. (119))

Bałaban's one-step averaging operator is written on *oriented contours*: the
two centre-to-point legs of a block, joined by the literal crossing bond, and
the Lie-algebra valued one-form is transported along such a contour by the
recursion

    R₀A (s :: F) = A s + Ad (U s) (R₀A F),        R₀A [] = 0 .

This file develops that calculus honestly on the periodic lattice `(ℤ/L)^d`,
with *signed* steps: a negatively oriented step really goes through the inverse
link, and the one-form really transforms with the covariant reversal law
`A (rev s) = - Ad (U s)⁻¹ (A s)`.  What is proved:

* `walk_append`, `hol_append`, `rzero_append` — the concatenation (composition)
  laws for the endpoint map, the holonomy, and the transported one-form.  The
  last one is the statement that `R₀A` of a concatenated contour is the first
  leg plus the *adjoint transport* of the second leg, i.e. exactly the algebra
  the source uses when it splits a contour at the crossing bond.
* `walk_revWord`, `hol_revWord`, `rzero_revWord` — orientation reversal really
  inverts: reversing a contour returns to its start, inverts the holonomy, and
  negates the transported one-form after adjoint transport.
* `walk_add`, `hol_translate`, `rzero_translate` — periodic translation
  covariance.  Its consequence `crossing_of_centres` is the statement that a
  *single* crossing word joining the two block centres transports **every**
  centred offset of the block: no point-by-point crossing datum is needed.
* `blockAverage_const`, `blockAverage_sum_eq` and `card_block` — the block
  average `Y = L^{-d} Σ_{x ∈ B(c₋)} Y_x` at the minimal lane `d = 4`, `L = 13`
  (`13⁴ = 28561`), together with the fact that it reproduces constants.

Nothing here is conditional: these are theorems about the transport calculus
itself.  They do **not** by themselves establish any Bałaban estimate; they
supply the algebraic layer that the analytic statements are written in.
-/
import Mathlib

namespace YangMills.CMP98Eq119

open Finset

/-! ## 1. Sites and oriented steps of the periodic lattice -/

/-- Sites of the periodic lattice `(ℤ/L)^d`. -/
abbrev PSite (d L : ℕ) := Fin d → ZMod L

/-- An oriented axial step: an axis together with an orientation
(`true` = forward, `false` = backward). -/
abbrev Step (d : ℕ) := Fin d × Bool

variable {d L : ℕ}

/-- The unit lattice vector along an axis. -/
def unitVec (μ : Fin d) : PSite d L := Pi.single μ (1 : ZMod L)

/-- The site reached from `x` by an oriented step. -/
def move (s : Step d) (x : PSite d L) : PSite d L :=
  if s.2 then x + unitVec s.1 else x - unitVec s.1

/-- The step with reversed orientation. -/
def revStep (s : Step d) : Step d := (s.1, !s.2)

@[simp] theorem revStep_revStep (s : Step d) : revStep (revStep s) = s := by
  cases s with
  | mk a b => cases b <;> rfl

@[simp] theorem move_revStep (s : Step d) (x : PSite d L) :
    move (revStep s) (move s x) = x := by
  cases s with
  | mk a b => cases b <;> simp [move, revStep]

@[simp] theorem revStep_fst (s : Step d) : (revStep s).1 = s.1 := rfl

theorem move_add (s : Step d) (x v : PSite d L) :
    move s (x + v) = move s x + v := by
  cases s with
  | mk a b => cases b <;> simp [move] <;> abel

/-- The endpoint of the contour that starts at `x` and follows the word `ss`. -/
def walk : PSite d L → List (Step d) → PSite d L
  | x, [] => x
  | x, s :: ss => walk (move s x) ss

@[simp] theorem walk_nil (x : PSite d L) : walk x [] = x := rfl

@[simp] theorem walk_cons (x : PSite d L) (s : Step d) (ss : List (Step d)) :
    walk x (s :: ss) = walk (move s x) ss := rfl

theorem walk_append (x : PSite d L) (ss tt : List (Step d)) :
    walk x (ss ++ tt) = walk (walk x ss) tt := by
  induction ss generalizing x with
  | nil => simp
  | cons s ss ih => simp [ih]

/-- Periodic translation covariance of the endpoint map. -/
theorem walk_add (x v : PSite d L) (ss : List (Step d)) :
    walk (x + v) ss = walk x ss + v := by
  induction ss generalizing x with
  | nil => simp
  | cons s ss ih => simp [move_add, ih]

/-- The orientation-reversed contour word. -/
def revWord (ss : List (Step d)) : List (Step d) :=
  (ss.map revStep).reverse

@[simp] theorem revWord_nil : revWord ([] : List (Step d)) = [] := rfl

theorem revWord_cons (s : Step d) (ss : List (Step d)) :
    revWord (s :: ss) = revWord ss ++ [revStep s] := by
  simp [revWord]

/-- Reversing a contour returns to its starting site. -/
@[simp] theorem walk_revWord (x : PSite d L) (ss : List (Step d)) :
    walk (walk x ss) (revWord ss) = x := by
  induction ss generalizing x with
  | nil => simp
  | cons s ss ih => simp [revWord_cons, walk_append, ih]

/-! ### The crossing of two block centres transports every centred offset

This is the statement that the point-by-point matching `x ↦ x'` used by the
source is *not* independent data: one crossing word between the two centres,
plus periodicity, moves the whole block. -/

theorem crossing_of_centres {cMinus cPlus : PSite d L} {cross : List (Step d)}
    (h : walk cMinus cross = cPlus) (p : PSite d L) :
    walk (cMinus + p) cross = cPlus + p := by
  rw [walk_add, h]

/-! ### Canonical axial words, block offsets, and the canonical coarse bond

The geometric data of the source is not a free choice either.  A *coarse bond*
is a straight signed segment of the block length along one axis; the
centre-to-point *legs* are the canonical axial words.  Both are constructed
here and their endpoints are computed, so that no "which contour joins the two
centres?" datum has to be supplied by a caller. -/

/-- The straight signed segment: `n` repetitions of one oriented step. -/
def axisSegment (s : Step d) (n : ℕ) : List (Step d) := List.replicate n s

@[simp] theorem axisSegment_length (s : Step d) (n : ℕ) :
    (axisSegment s n).length = n := by
  simp [axisSegment]

theorem walk_axisSegment_forward (x : PSite d L) (a : Fin d) (k : ℕ) :
    walk x (axisSegment (a, true) k) = x + k • unitVec a := by
  induction k generalizing x with
  | zero => simp [axisSegment]
  | succ k ih =>
      rw [axisSegment, List.replicate_succ, walk_cons, ← axisSegment, ih]
      have hmove : move ((a, true) : Step d) x = x + unitVec a := rfl
      rw [hmove, succ_nsmul]
      abel

theorem walk_axisSegment_backward (x : PSite d L) (a : Fin d) (k : ℕ) :
    walk x (axisSegment (a, false) k) = x - k • unitVec a := by
  induction k generalizing x with
  | zero => simp [axisSegment]
  | succ k ih =>
      rw [axisSegment, List.replicate_succ, walk_cons, ← axisSegment, ih]
      have hmove : move ((a, false) : Step d) x = x - unitVec a := rfl
      rw [hmove, succ_nsmul]
      abel

/-- The `13⁴` offsets of one block. -/
abbrev BlockOffset := PSite 4 13

/-- The embedding of a block offset into the fine torus `(ℤ/N)⁴`.  Block sites
are `c₋ + embedOffset p`; for `13 ≤ N` this is injective, so the block really
carries `13⁴ = 28561` distinct sites and is *not* all of the torus. -/
def embedOffset {N : ℕ} (p : BlockOffset) : PSite 4 N := fun a => ((p a).val : ZMod N)

theorem embedOffset_injective {N : ℕ} (hN : 13 ≤ N) :
    Function.Injective (embedOffset (N := N)) := by
  haveI : NeZero N := ⟨by omega⟩
  intro p q h
  funext a
  have h' : ((p a).val : ZMod N) = ((q a).val : ZMod N) := congrFun h a
  have hp : (p a).val < N := lt_of_lt_of_le (ZMod.val_lt _) hN
  have hq : (q a).val < N := lt_of_lt_of_le (ZMod.val_lt _) hN
  have hv := congrArg ZMod.val h'
  rw [ZMod.val_cast_of_lt hp, ZMod.val_cast_of_lt hq] at hv
  exact ZMod.val_injective 13 hv

/-- The canonical centre-to-point leg: walk `(p a)` forward steps along each
axis in turn. -/
def legWord (p : BlockOffset) : List (Step 4) :=
  (List.finRange 4).flatMap (fun a => axisSegment (a, true) (p a).val)

theorem sum_val_smul_unitVec {N : ℕ} (p : BlockOffset) :
    (p 0).val • unitVec (L := N) (0 : Fin 4) + (p 1).val • unitVec (L := N) (1 : Fin 4)
        + (p 2).val • unitVec (L := N) (2 : Fin 4) + (p 3).val • unitVec (L := N) (3 : Fin 4)
      = embedOffset p := by
  funext b
  simp only [Pi.add_apply, Pi.smul_apply, embedOffset]
  fin_cases b <;> simp [unitVec, nsmul_eq_mul]

/-- The canonical leg really goes from a site to that site displaced by the
embedded block offset — for all `13⁴` offsets at once, by construction. -/
theorem walk_legWord {N : ℕ} (x : PSite 4 N) (p : BlockOffset) :
    walk x (legWord p) = x + embedOffset p := by
  have hfr : (List.finRange 4) = [0, 1, 2, 3] := by decide
  have hsum := sum_val_smul_unitVec (N := N) p
  rw [legWord, hfr]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [walk_append, walk_append, walk_append, walk_axisSegment_forward,
    walk_axisSegment_forward, walk_axisSegment_forward, walk_axisSegment_forward]
  conv_rhs => rw [← hsum]
  abel

/-- The canonical coarse bond at the minimal lane: the straight signed segment
of length `13` (the block size) along one axis.  Only the axis and the
orientation are data; the length and the word are constructed. -/
def coarseBond (μ : Fin 4) (o : Bool) : List (Step 4) := axisSegment (μ, o) 13

/-- The neighbouring block centre reached by the canonical coarse bond. -/
def nextCentre {N : ℕ} (cMinus : PSite 4 N) (μ : Fin 4) (o : Bool) : PSite 4 N :=
  if o then cMinus + (13 : ℕ) • unitVec μ else cMinus - (13 : ℕ) • unitVec μ

/-- The canonical coarse bond joins the two block centres.  This is a
computation, not a hypothesis. -/
theorem walk_coarseBond {N : ℕ} (cMinus : PSite 4 N) (μ : Fin 4) (o : Bool) :
    walk cMinus (coarseBond μ o) = nextCentre cMinus μ o := by
  cases o with
  | false => simpa [coarseBond, nextCentre] using walk_axisSegment_backward cMinus μ 13
  | true => simpa [coarseBond, nextCentre] using walk_axisSegment_forward cMinus μ 13

/-- At any torus size `N > 13` the two block centres are genuinely distinct:
the coarse bond is not a degenerate loop. -/
theorem nextCentre_ne {N : ℕ} (hN : 13 < N) (cMinus : PSite 4 N) (μ : Fin 4) :
    nextCentre cMinus μ true ≠ cMinus := by
  haveI : NeZero N := ⟨by omega⟩
  intro h
  rw [nextCentre, if_pos rfl] at h
  have h' : ((13 : ℕ) • unitVec (L := N) μ) = 0 := by
    have := congrArg (fun y => y - cMinus) h
    simpa using this
  have hcomp : ((13 : ℕ) : ZMod N) = 0 := by
    have := congrFun h' μ
    simpa [unitVec, nsmul_eq_mul] using this
  have hcast : ((13 : ℕ) : ZMod N) = ((0 : ℕ) : ZMod N) := by simpa using hcomp
  have hval := congrArg ZMod.val hcast
  rw [ZMod.val_cast_of_lt hN, ZMod.val_cast_of_lt (by omega : 0 < N)] at hval
  exact absurd hval (by omega)

/-! ## 2. Signed links and holonomy -/

variable {G : Type*} [Group G]

/-- A link field on oriented steps is *signed* when a reversed step carries the
inverse group element — the repository's inverse-oriented link convention. -/
def SignedLink (link : PSite d L → Step d → G) : Prop :=
  ∀ x s, link (move s x) (revStep s) = (link x s)⁻¹

/-- The holonomy of the contour starting at `x` with word `ss`. -/
def hol (link : PSite d L → Step d → G) : PSite d L → List (Step d) → G
  | _, [] => 1
  | x, s :: ss => link x s * hol link (move s x) ss

variable (link : PSite d L → Step d → G)

@[simp] theorem hol_nil (x : PSite d L) : hol link x [] = 1 := rfl

@[simp] theorem hol_cons (x : PSite d L) (s : Step d) (ss : List (Step d)) :
    hol link x (s :: ss) = link x s * hol link (move s x) ss := rfl

theorem hol_append (x : PSite d L) (ss tt : List (Step d)) :
    hol link x (ss ++ tt) = hol link x ss * hol link (walk x ss) tt := by
  induction ss generalizing x with
  | nil => simp
  | cons s ss ih => simp [ih, mul_assoc]

/-- Orientation reversal inverts the holonomy — through the genuine inverse
links, not by fiat. -/
theorem hol_revWord (hlink : SignedLink link) (x : PSite d L)
    (ss : List (Step d)) :
    hol link (walk x ss) (revWord ss) = (hol link x ss)⁻¹ := by
  induction ss generalizing x with
  | nil => simp
  | cons s ss ih =>
      rw [walk_cons, revWord_cons, hol_append, ih]
      simp [walk_revWord, hlink x s, mul_inv_rev]

/-- Translation covariance of the holonomy, for a periodic link field. -/
theorem hol_translate (v : PSite d L)
    (hper : ∀ x s, link (x + v) s = link x s) (x : PSite d L)
    (ss : List (Step d)) :
    hol link (x + v) ss = hol link x ss := by
  induction ss generalizing x with
  | nil => simp
  | cons s ss ih => rw [hol_cons, hol_cons, hper, move_add, ih]

/-! ## 3. The transported one-form `R₀A` -/

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem rho_apply_inv (rho : G →* V →ₗ[ℝ] V) (g : G) (v : V) :
    rho g (rho g⁻¹ v) = v := by
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

theorem rho_inv_apply (rho : G →* V →ₗ[ℝ] V) (g : G) (v : V) :
    rho g⁻¹ (rho g v) = v := by
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

/-- A Lie-algebra valued one-form on oriented steps is *covariantly signed*
when reversing a step negates the value after transporting it back with the
inverse link.  This is the convention that makes `R₀A` orientation-consistent. -/
def CovariantForm (link : PSite d L → Step d → G) (rho : G →* V →ₗ[ℝ] V)
    (A : PSite d L → Step d → V) : Prop :=
  ∀ x s, A (move s x) (revStep s) = - rho (link x s)⁻¹ (A x s)

/-- Bałaban's transported one-form: `R₀A (s :: F) = A s + Ad (U s) (R₀A F)`. -/
def rzero (link : PSite d L → Step d → G) (rho : G →* V →ₗ[ℝ] V)
    (A : PSite d L → Step d → V) : PSite d L → List (Step d) → V
  | _, [] => 0
  | x, s :: ss => A x s + rho (link x s) (rzero link rho A (move s x) ss)

variable (rho : G →* V →ₗ[ℝ] V) (A : PSite d L → Step d → V)

@[simp] theorem rzero_nil (x : PSite d L) : rzero link rho A x [] = 0 := rfl

@[simp] theorem rzero_cons (x : PSite d L) (s : Step d) (ss : List (Step d)) :
    rzero link rho A x (s :: ss)
      = A x s + rho (link x s) (rzero link rho A (move s x) ss) := rfl

/-- The concatenation law: the transported form of a contour split at any bond
is the first leg plus the adjoint transport of the second leg. -/
theorem rzero_append (x : PSite d L) (ss tt : List (Step d)) :
    rzero link rho A x (ss ++ tt)
      = rzero link rho A x ss
        + rho (hol link x ss) (rzero link rho A (walk x ss) tt) := by
  induction ss generalizing x with
  | nil => simp
  | cons s ss ih =>
      simp only [List.cons_append, rzero_cons, walk_cons, hol_cons, ih,
        map_add, map_mul, Module.End.mul_apply]
      abel

/-- Orientation reversal negates the transported one-form, after adjoint
transport by the holonomy of the forward contour. -/
theorem rzero_revWord (hlink : SignedLink link)
    (hA : CovariantForm link rho A) (x : PSite d L) (ss : List (Step d)) :
    rho (hol link x ss) (rzero link rho A (walk x ss) (revWord ss))
      = - rzero link rho A x ss := by
  induction ss generalizing x with
  | nil => simp
  | cons s ss ih =>
      have hlast : rzero link rho A (move s x) [revStep s]
          = - rho (link x s)⁻¹ (A x s) := by
        simp [rzero, hA x s]
      rw [walk_cons, revWord_cons, rzero_append, walk_revWord, hlast,
        hol_revWord link hlink, hol_cons]
      simp only [map_mul, Module.End.mul_apply, map_add, map_neg, ih,
        rho_apply_inv, rzero_cons]
      abel

/-! ## 4. The block average at the minimal lane `d = 4`, `L = 13` -/

/-- The number of fine sites in one `13⁴` block. -/
theorem card_block : Fintype.card (PSite 4 13) = 28561 := by
  simp [PSite]


/-- `Y = L^{-d} Σ_{x ∈ B(c₋)} Y_x`, the block average that Bałaban's outer Lie
element is *constructed* from (rather than chosen independently). -/
noncomputable def blockAverage (Y : PSite 4 13 → V) : V :=
  ((28561 : ℝ)⁻¹) • ∑ x : PSite 4 13, Y x

theorem blockAverage_sum_eq (Y : PSite 4 13 → V) :
    (28561 : ℝ) • blockAverage Y = ∑ x : PSite 4 13, Y x := by
  rw [blockAverage, smul_smul]
  norm_num

/-- The block average reproduces constants: the normalisation `1/28561` is the
correct one for a `13⁴` block. -/
theorem blockAverage_const (v : V) : blockAverage (fun _ : PSite 4 13 => v) = v := by
  rw [blockAverage, Finset.sum_const, Finset.card_univ, card_block,
    ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  norm_num

end YangMills.CMP98Eq119
