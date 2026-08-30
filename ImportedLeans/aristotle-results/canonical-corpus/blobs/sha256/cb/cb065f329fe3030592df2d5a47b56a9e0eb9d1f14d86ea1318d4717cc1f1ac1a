import Synthesis.WalkGeometry
import Synthesis.MoonshineBase

/-!
# Synthesis layer 2''': arithmetic semantics for the walk lens

The supplied `AgdaMirror.MonsterWalk` walk is driven by a `Lens` whose
`admissible : State → Mask → Bool` field is *uninterpreted*: nothing in the
source material says which moves the walk is allowed to make.  That left the
walk formally disconnected from the mask arithmetic of `Synthesis.MoonshineBase`
and from the mask geometry of `Synthesis.MonsterFibre`.

This file supplies the missing interpretation and proves that it has the
expected geometric consequence.

* `maskProduct_dvd_iff` (in `MoonshineBase`) is the enabling fact: because the
  base is fifteen *distinct primes*, divisibility of mask products **is** the
  submask relation.
* `arithLens` reads admissibility arithmetically: a move to `m` is admissible
  exactly when `m`'s prime product divides the current state's.  By the above
  this says precisely that the move only *removes* prime factors.
* `step_arith_dvd` / `orbit_arith_dvd`: every step, and hence every state of
  every orbit, descends in this divisibility order.
* `step_arith_submask`: therefore every step descends in the submask order.
* `step_arith_dSSP_empty_le` / `orbit_arith_dSSP_empty_le`: therefore the walk
  is **non-expanding towards the collapse mask** in the supplied ultrametric.
  This is the metric statement the uninterpreted lens could not support.

Boundary: this is an interpretation *we supply*, not one recovered from the
source material; it is stated as a definition (`arithLens`) and everything about
it is proved, but the source material makes no claim that this is "the" lens.
-/

namespace Synthesis.WalkArithmetic

open AgdaMirror.MonsterOntos (SSP)
open AgdaMirror.MonsterWalk (Mask State Lens Candidates choose step orbit)
open Synthesis.MonsterFibre
open Synthesis.MoonshineBase

/-! ## Reading a raw walk mask over the prime base -/

/-- A raw boolean list read as a mask over the prime base (out-of-range slots
count as removed). -/
def maskOfList (l : List Bool) : MaskSSP := fun p => l.getD (sspToFin p) false

/-- On length-15 lists this reading is the supplied mask carrier identification. -/
theorem maskOfList_eq (l : List Bool) (h : l.length = 15) :
    maskOfList l = maskFibreEquiv.symm ⟨l, h⟩ := by
  funext p
  have hlt : (sspToFin p : Nat) < l.length := by rw [h]; exact (sspToFin p).isLt
  show l.getD (sspToFin p) false = _
  rw [List.getD_eq_getElem l false hlt]
  rfl

/-- The arithmetic weight of a raw walk mask: the product of the primes it keeps. -/
def listProduct (l : List Bool) : Nat := maskProduct (maskOfList l)

/-! ## The arithmetic lens -/

/-- **The arithmetic lens.**  A move is admissible exactly when it only removes
prime factors, tested by divisibility of mask products. -/
def arithLens : Lens := ⟨fun s m => decide (listProduct m ∣ listProduct s.mask)⟩

/-- Whatever the candidate list, the chosen mask descends in the divisibility
order. -/
theorem choose_arith_dvd (s : State) :
    ∀ cands : Candidates, listProduct (choose arithLens s cands s.mask) ∣ listProduct s.mask := by
  intro cands
  induction cands with
  | nil => exact dvd_rfl
  | cons m ms ih =>
    by_cases hm : arithLens.admissible s m = true
    · simp only [choose, hm, if_true]
      simpa [arithLens] using hm
    · simp only [Bool.not_eq_true] at hm
      simpa [choose, hm] using ih

/-- **Every arithmetic step removes factors.** -/
theorem step_arith_dvd (cands : Candidates) (s : State) :
    listProduct (step arithLens cands s).mask ∣ listProduct s.mask :=
  choose_arith_dvd s cands

/-- Every state of every orbit descends from the seed. -/
theorem orbit_arith_dvd (cands : Candidates) :
    ∀ (n : Nat) (s t : State), t ∈ orbit arithLens cands n s →
      listProduct t.mask ∣ listProduct s.mask := by
  intro n
  induction n with
  | zero =>
    intro s t ht
    simp only [orbit, List.mem_singleton] at ht
    subst ht; exact dvd_rfl
  | succ n ih =>
    intro s t ht
    simp only [orbit, List.mem_cons] at ht
    rcases ht with rfl | ht
    · exact dvd_rfl
    · exact (ih (step arithLens cands s) t ht).trans (step_arith_dvd cands s)

/-! ## Geometric consequence -/

/-- The arithmetic descent is a submask descent. -/
theorem step_arith_submask (cands : Candidates) (s : State) (p : SSP) :
    maskOfList (step arithLens cands s).mask p = true → maskOfList s.mask p = true :=
  (maskProduct_dvd_iff _ _).mp (step_arith_dvd cands s) p

/-- **The arithmetic walk is non-expanding towards the collapse mask.**  This is
the geometric content the uninterpreted lens could not supply: with arithmetic
admissibility, one step never increases the supplied ultrametric distance to the
empty mask. -/
theorem step_arith_dSSP_empty_le (cands : Candidates) (s : State) :
    dSSP (maskOfList (step arithLens cands s).mask) emptyMaskSSP ≤
      dSSP (maskOfList s.mask) emptyMaskSSP :=
  dSSP_empty_mono (step_arith_submask cands s)

/-- The same for every state of every orbit. -/
theorem orbit_arith_dSSP_empty_le (cands : Candidates) (n : Nat) (s t : State)
    (ht : t ∈ orbit arithLens cands n s) :
    dSSP (maskOfList t.mask) emptyMaskSSP ≤ dSSP (maskOfList s.mask) emptyMaskSSP :=
  dSSP_empty_mono ((maskProduct_dvd_iff _ _).mp (orbit_arith_dvd cands n s t ht))

end Synthesis.WalkArithmetic
