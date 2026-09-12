import Mathlib
import AgdaMirror.Ultrametric

/-!
# Lean mirror of the `Monster/` walk subdirectory (genuine + honest scaffolding)

Faithful transcription of the `Monster.Mask`, `Monster.Ultrametric`
(= `Monster.MUltrametric`), `Monster.Step`, `Monster.Trace`,
`Monster.TraceSound` and `Monster.Projection` Agda modules, together with the
relevant pieces of the top-level `MonsterState` module.

These model the DASHI "monster walk": the 15 prime-power factors of `|M|` as a
length-15 boolean *mask*, a deterministic `step` selecting the first admissible
candidate mask via a measurement `Lens`, the resulting orbit `Trace`, the
adjacent-step soundness relation `StepOK`, and the first-difference "distance"
`dMask` on masks.

## Honesty boundary

The Agda `Monster.Ultrametric`/`Monster.MUltrametric` modules **postulate** two
laws of `dMask`: symmetry (`symMask`) and the ultrametric triangle inequality
(`ultraMask`).  Examining the actual definition:

* `symMask` is in fact **true**, so here it is *proved* (`dMask_symm`), turning
  that postulate into genuine content.
* `ultraMask` is in fact **false** for this `dMask` (which measures the length
  of the common prefix, so two very different masks can share a long prefix
  while a third mask agrees with neither): this is *disproved*
  (`dMask_ultratriangle_false`).  Accordingly the `Ultrametric Mask` bundle is
  built only by *taking the ultratriangle law as an explicit hypothesis*
  (`UMask`), never as an axiom — exactly the honesty discipline used elsewhere
  in `AgdaMirror`.
-/

namespace AgdaMirror.MonsterWalk

/-! ## `Monster.Mask` / `MonsterState`: masks over the 15 prime-power factors -/

/-- The 15 prime-power factors of `|M|`. -/
def FactorCount : Nat := 15

/-- A mask is a boolean list (`true` = keep factor, `false` = remove factor). -/
abbrev Mask := List Bool

/-- `replicate n b` — a length-`n` constant mask. -/
def replicate : Nat → Bool → Mask
  | 0,     _ => []
  | n + 1, b => b :: replicate n b

/-- Canonical full mask (all 15 factors kept). -/
def fullMask : Mask := replicate FactorCount true

/-- Collapse mask (all factors removed). -/
def emptyMask : Mask := replicate FactorCount false

/-- Boolean AND (Agda `boolAnd`). -/
def boolAnd : Bool → Bool → Bool
  | true, true => true
  | _,    _    => false

/-- Boolean negation (Agda `notBool`). -/
def notBool : Bool → Bool
  | true  => false
  | false => true

/-- Pointwise AND of masks (factor-removal composition). -/
def maskAnd : Mask → Mask → Mask
  | [],      []      => []
  | b :: xs, c :: ys => boolAnd b c :: maskAnd xs ys
  | _,       _       => []

/-- Involution: flip keep/remove. -/
def flipMask : Mask → Mask
  | []      => []
  | b :: xs => notBool b :: flipMask xs

/-- `flipMask` is an involution. -/
theorem flipMask_flipMask (m : Mask) : flipMask (flipMask m) = m := by
  induction m with
  | nil => rfl
  | cons b xs ih => cases b <;> simp [flipMask, notBool, ih]

/-- A kernel-style mask operator. -/
structure Kernel where
  K : Mask → Mask

/-- Projection to a fixed target mask. -/
def projectTo (target : Mask) : Kernel := ⟨fun _ => target⟩

/-! ## `MonsterState`: walk state, lens, candidates -/

/-- Walk state: a mask together with an abstract digit-window index. -/
structure State where
  mask : Mask
  window : Nat

/-- A lens is the measurement predicate: is removing to mask `m` admissible? -/
structure Lens where
  admissible : State → Mask → Bool

/-- Candidate moves: a finite list of candidate masks. -/
abbrev Candidates := List Mask

/-! ## `Monster.Step`: deterministic step and iteration -/

/-- First admissible candidate (leftmost wins); else `fallback`. -/
def choose (L : Lens) (s : State) : Candidates → Mask → Mask
  | [],      fallback => fallback
  | m :: ms, fallback => if L.admissible s m then m else choose L s ms fallback

/-- One deterministic walk step: pick next mask via the lens, advance window. -/
def step (L : Lens) (cands : Candidates) (s : State) : State :=
  ⟨choose L s cands s.mask, s.window + 1⟩

/-- Structural iteration of a self-map. -/
def iterate {A : Type} (f : A → A) : Nat → A → A
  | 0,     x => x
  | n + 1, x => iterate f n (f x)

/-- The window strictly advances on every step. -/
theorem step_window (L : Lens) (cands : Candidates) (s : State) :
    (step L cands s).window = s.window + 1 := rfl

/-! ## `Monster.Trace` / `Monster.TraceSound`: traces and step soundness -/

/-- A trace is a (here, possibly empty) list of states. -/
abbrev Trace := List State

/-- Adjacent-step soundness over a trace: each state is the `step` of the prior.

Mirrors `Monster.TraceSound.StepOK`. -/
inductive StepOK (L : Lens) (cands : Candidates) : List State → Prop
  | ok0 {s : State} : StepOK L cands [s]
  | okCons {s₀ s₁ : State} {ss : List State} :
      step L cands s₀ = s₁ → StepOK L cands (s₁ :: ss) →
      StepOK L cands (s₀ :: s₁ :: ss)

/-- The orbit segment of length `n + 1` produced by iterating `step` from a seed. -/
def orbit (L : Lens) (cands : Candidates) : Nat → State → List State
  | 0,     s => [s]
  | n + 1, s => s :: orbit L cands n (step L cands s)

/-- The orbit of `step` from a seed is always step-sound (a genuine MW-00 fact,
left abstract in the Agda original). -/
theorem stepOK_orbit (L : Lens) (cands : Candidates) (s : State) (n : Nat) :
    StepOK L cands (orbit L cands n s) := by
  induction n generalizing s with
  | zero => exact StepOK.ok0
  | succ m ih =>
    cases m with
    | zero => exact StepOK.okCons rfl StepOK.ok0
    | succ k =>
      exact StepOK.okCons rfl (ih (step L cands s))

/-! ## `Monster.Ultrametric`: first-difference distance on masks -/

/-- Index of the first differing bit (Agda `firstDiff`); `0` if identical. -/
def firstDiff : Mask → Mask → Nat → Nat
  | [],          [],          _ => 0
  | true :: xs,  true :: ys,  n => firstDiff xs ys (n + 1)
  | false :: xs, false :: ys, n => firstDiff xs ys (n + 1)
  | _,           _,           n => n

/-- First-difference "distance" on masks. -/
def dMask (x y : Mask) : Nat := firstDiff x y 0

/-- `firstDiff m m n = 0`: identical masks have first-difference `0`. -/
theorem firstDiff_self_zero (m : Mask) (n : Nat) : firstDiff m m n = 0 := by
  induction m generalizing n with
  | nil => rfl
  | cons b xs ih => cases b <;> simp [firstDiff, ih]

/-- Identity-of-indiscernibles direction: `dMask m m = 0`. -/
theorem dMask_id_zero (m : Mask) : dMask m m = 0 := firstDiff_self_zero m 0

/-- The postulated symmetry `symMask` is in fact **provable**. -/
theorem firstDiff_symm (x y : Mask) (n : Nat) : firstDiff x y n = firstDiff y x n := by
  induction x generalizing y n with
  | nil => cases y <;> simp [firstDiff]
  | cons b xs ih =>
    cases y with
    | nil => cases b <;> simp [firstDiff]
    | cons c ys => cases b <;> cases c <;> simp [firstDiff, ih]

/-- Symmetry of `dMask` (the genuine version of the Agda `symMask` postulate). -/
theorem dMask_symm (x y : Mask) : dMask x y = dMask y x := firstDiff_symm x y 0

/-- The postulated ultrametric triangle law `ultraMask` is in fact **false**:
`dMask` measures the common-prefix length, so two masks sharing a long prefix can
be far (in the ultrametric sense) from a third mask that agrees with neither. -/
theorem dMask_ultratriangle_false :
    ¬ (∀ x y z : Mask, dMask x z ≤ max (dMask x y) (dMask y z)) := by
  intro h
  exact absurd (h [true, true, false] [false] [true, true, true]) (by decide)

/-- The `Ultrametric Mask` bundle, built by *taking the ultratriangle law as an
explicit hypothesis* (it is genuinely false for `dMask`; see
`dMask_ultratriangle_false`).  Symmetry and identity are supplied by the proved
lemmas above. -/
def UMask
    (ultratriangle : ∀ x y z : Mask, dMask x z ≤ max (dMask x y) (dMask y z)) :
    AgdaMirror.Ultrametric Mask where
  d := dMask
  id_zero := dMask_id_zero
  symmetric := dMask_symm
  ultratriangle := ultratriangle

/-! ## `Monster.Projection`: unique fixed point of a constant projection -/

/-- A fixed point of a mask operator. -/
def Fixed (K : Mask → Mask) (m : Mask) : Prop := K m = m

/-- Any two fixed points of a constant projection coincide
(Agda `uniqueFixedProj`). -/
theorem uniqueFixedProj (target x y : Mask)
    (fx : Fixed (projectTo target).K x) (fy : Fixed (projectTo target).K y) :
    x = y := by
  simp only [Fixed, projectTo] at fx fy
  exact fx.symm.trans fy

end AgdaMirror.MonsterWalk
