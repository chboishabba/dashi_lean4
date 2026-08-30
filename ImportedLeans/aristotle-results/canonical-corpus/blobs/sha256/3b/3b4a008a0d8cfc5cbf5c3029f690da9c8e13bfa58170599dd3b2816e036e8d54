import Cuisine.NineSheet

/-!
# The supervoxel lane: constraint refinement, clopen ternary balls, and cuisine

This module audits the *supervoxel* material of the Agda corpus
(`DASHI.Foundations.ConstraintClopenRefinement`, used by
`DASHI.Cognition.ClopenPsychologicalSupervoxel` and
`DASHI.Unified.ChemistrySupervoxel`) and connects it to the cuisine transport of
`Cuisine.UmamiTransport`.

What the Agda supplies is an *interface*: a `ConstraintSystem` record
(states, constraints, a satisfaction relation), a refinement relation
`FineExtendsCoarse`, admissible regions as Σ-types, and a `ClopenBallSystem`
record whose branching type `BTBranch` is three-element.  Its two substantive
side-conditions are `childContained` (a child ball sits inside its parent) and
`childCover` (the three children cover the parent).  Everything else in that
record — in particular the `ballOpen` / `ballClosed` fields — is a bare
`Set`-valued field with no imposed law, i.e. an authority annotation, and the
psychological instance records non-atomicity of the coarse "public zero" as a
`Bool` field pinned to `false`, not as a theorem.

Proved here (all sorry-free):

* the mirror of the interface, with `fineExtendsCoarse_refl` / `_trans`
  (refinement is a preorder) and `refinedRegionInclusion_injective`;
* `cuisineNeutrality` — a *cuisine* constraint system: states are umami
  intensities, constraints are subsets of the fifteen supersingular primes, and
  a blend satisfies a constraint when its hyperfabric shadow is neutral on that
  subset;
* `neutrality_refines_iff` — **the supervoxel refinement order on these
  constraints is exactly the Monster mask lattice order**.  The nontrivial
  direction needs surjectivity of the cuisine transport
  (`Cuisine.UmamiTransport.umamiFabric_surjective`), so this is a genuine use of
  the cuisine material, not a restatement of set inclusion;
* `card_neutralFabric` — the admissible region of a constraint has `3 ^ k`
  hyperfabric shadows, `k` the number of primes the constraint leaves free;
* `btBranchEquivTrit` — the Agda branch type *is* the balanced-ternary digit of
  `AgdaMirror.DASHIAlgebra`, in the enumeration order of both files;
* `ternaryBallSystem` — a checked instance of the clopen-ball interface: points
  are ternary streams, balls are prefix agreement, children are digit updates.
  `cyl_child_cover` and `cyl_child_contained` are proved, not postulated;
* `no_atomic_ball`, `children_disjoint` — **every ball splits into exactly three
  pairwise disjoint, inhabited child balls**, so no ball is atomic.  This is the
  theorem the Agda states as the `Bool` field
  `publicZeroIsAtomic ≡ false`;
* `ball_complement_union` — the combinatorial content of clopenness: the
  complement of a ball is a union of balls of the same depth;
* `umamiFabric_eq_iff_ball` — **the cuisine transport is the depth-15 ball
  projection**: two blends have the same hyperfabric shadow exactly when their
  ternary streams lie in a common depth-15 ball;
* `cuisine_supervoxel_not_atomic` — an explicit pair of distinct cuisine
  intensities in one depth-15 ball, so the coarse-graining is genuinely lossy.

Boundary.  Nothing here is a claim about psychology, chemistry or food.  The
Agda's psychological instance is *not* mirrored: it depends on a hidden-state
record whose fields are uninterpreted, and the two refinement lemmas it proves
are `cong`/`trans` bookkeeping.  What is transported is the interface and its
ternary branching, and the statement that the cuisine transport is an instance
of it.
-/

namespace Cuisine.SupervoxelClopen

open AgdaMirror.DASHIAlgebra (Trit)
open AgdaMirror.MonsterOntos (SSP)
open Synthesis.MonsterFibre
open Synthesis.Hyperfabric
open Cuisine.UmamiTransport
open Cuisine.NineSheet

/-! ## The interface, mirrored -/

/-- Mirror of `DASHI.Foundations.ConstraintClopenRefinement.ConstraintSystem`. -/
structure ConstraintSystem where
  State : Type
  Constraint : Type
  satisfies : State → Constraint → Prop

/-- Mirror of `FineExtendsCoarse`: the fine constraint implies the coarse one. -/
structure FineExtendsCoarse (S : ConstraintSystem) (coarse fine : S.Constraint) : Prop where
  forgetConstraint : ∀ {state : S.State}, S.satisfies state fine → S.satisfies state coarse

/-- Mirror of `AdmissibleRegion`: the states satisfying a constraint. -/
abbrev AdmissibleRegion (S : ConstraintSystem) (c : S.Constraint) : Type :=
  {state : S.State // S.satisfies state c}

/-- Mirror of `refinedRegionInclusion`. -/
def refinedRegionInclusion {S : ConstraintSystem} {coarse fine : S.Constraint}
    (r : FineExtendsCoarse S coarse fine) (x : AdmissibleRegion S fine) :
    AdmissibleRegion S coarse :=
  ⟨x.1, r.forgetConstraint x.2⟩

@[simp] theorem refinedRegionInclusion_val {S : ConstraintSystem} {coarse fine : S.Constraint}
    (r : FineExtendsCoarse S coarse fine) (x : AdmissibleRegion S fine) :
    (refinedRegionInclusion r x).1 = x.1 := rfl

/-- Region inclusion really is an inclusion: it keeps the state. -/
theorem refinedRegionInclusion_injective {S : ConstraintSystem} {coarse fine : S.Constraint}
    (r : FineExtendsCoarse S coarse fine) :
    Function.Injective (refinedRegionInclusion r) := by
  intro x y h
  simpa [refinedRegionInclusion, Subtype.ext_iff] using h

/-- Refinement is reflexive. -/
theorem fineExtendsCoarse_refl (S : ConstraintSystem) (c : S.Constraint) :
    FineExtendsCoarse S c c := ⟨id⟩

/-- Refinement is transitive: a preorder on constraints. -/
theorem fineExtendsCoarse_trans {S : ConstraintSystem} {a b c : S.Constraint}
    (hab : FineExtendsCoarse S a b) (hbc : FineExtendsCoarse S b c) :
    FineExtendsCoarse S a c :=
  ⟨fun h => hab.forgetConstraint (hbc.forgetConstraint h)⟩

/-! ## A cuisine constraint system

States are umami intensities; constraints are subsets of the fifteen
supersingular primes; a blend satisfies a constraint when its hyperfabric shadow
is neutral (the digit `Trit.neg`, the neutral element of ternary XOR) at every
prime of the subset. -/

/-- A blend is *neutral on* a mask when its hyperfabric shadow vanishes there. -/
def NeutralOn (u : ℕ) (m : MaskSSP) : Prop :=
  ∀ p : SSP, m p = true → umamiFabric u p = Trit.neg

/-- The cuisine constraint system. -/
def cuisineNeutrality : ConstraintSystem where
  State := ℕ
  Constraint := MaskSSP
  satisfies := NeutralOn

/-- Larger masks are finer constraints. -/
theorem neutrality_refines_of_subset {m m' : MaskSSP} (h : ∀ p, m p = true → m' p = true) :
    FineExtendsCoarse cuisineNeutrality m m' :=
  ⟨fun {_} hfine p hp => hfine p (h p hp)⟩

/-- **The supervoxel refinement order on cuisine neutrality constraints is the
Monster mask lattice order.**  The forward direction uses surjectivity of the
cuisine transport: for each prime left out of `m'` there is an actual blend
whose shadow is non-neutral exactly there. -/
theorem neutrality_refines_iff (m m' : MaskSSP) :
    FineExtendsCoarse cuisineNeutrality m m' ↔ ∀ p, m p = true → m' p = true := by
  refine ⟨?_, neutrality_refines_of_subset⟩
  intro h p hp
  by_contra hp'
  have hfalse : m' p = false := Bool.eq_false_iff.mpr hp'
  classical
  set F : Fabric := fun q => if q = p then Trit.pos else Trit.neg with hF
  set u : ℕ := fabricIntensity F with hu
  have hUF : umamiFabric u = F := umamiFabric_fabricIntensity F
  have hfine : cuisineNeutrality.satisfies u m' := by
    intro q hq
    have hqp : q ≠ p := by
      intro hqp; rw [hqp, hfalse] at hq; exact Bool.noConfusion hq
    simp [hUF, hF, hqp]
  have hcoarse := h.forgetConstraint hfine
  have := hcoarse p hp
  rw [hUF] at this
  simp [hF] at this

/-- The hyperfabric shadows admitted by a constraint are the sections supported
off the constraint's mask; there are `3 ^ k` of them, `k` the number of primes
the constraint leaves free. -/
theorem card_neutralFabric (m : MaskSSP) :
    Fintype.card {F : Fabric // ∀ p : SSP, m p = true → F p = Trit.neg}
      = 3 ^ (Finset.univ.filter (fun p : SSP => m p = false)).card := by
  classical
  have hequiv :
      {F : Fabric // ∀ p : SSP, m p = true → F p = Trit.neg}
        ≃ Supported (Finset.univ.filter (fun p : SSP => m p = false)) := by
    refine Equiv.subtypeEquivRight ?_
    intro F
    constructor
    · intro h p hp
      have : m p = true := by
        by_contra hm
        exact hp (Finset.mem_filter.mpr ⟨Finset.mem_univ p, Bool.eq_false_iff.mpr hm⟩)
      exact h p this
    · intro h p hp
      refine h p ?_
      intro hmem
      have := (Finset.mem_filter.mp hmem).2
      rw [hp] at this
      exact Bool.noConfusion this
  rw [Fintype.card_congr hequiv, card_supported]

/-- A constraint is *atomic* when it pins down its state completely.  The
supervoxel claim of the Agda lane is that the coarse constraints of interest are
**not** atomic; in this repository that is a theorem for each instance, not a
`Bool` field. -/
def Atomic (S : ConstraintSystem) (c : S.Constraint) : Prop :=
  ∀ x y : AdmissibleRegion S c, x.1 = y.1

/-- **No cuisine neutrality constraint is atomic.**  The neutral shadow is
reached by distinct intensities — here `0` and `1 ⊕ 1 ⊕ 1 = 7` — and it
satisfies every constraint. -/
theorem cuisineNeutrality_not_atomic (m : MaskSSP) : ¬ Atomic cuisineNeutrality m := by
  have hzero : umamiFabric 0 = fabricZero := by
    apply fabricZMod.injective
    rw [fabricZMod_umamiFabric, fabricZMod_zero]
    funext p
    simp [toneAt]
  have hcube : umamiFabric (umamiCompose 1 (umamiCompose 1 1)) = fabricZero :=
    umamiFabric_cube 1
  have h0 : NeutralOn 0 m := by
    intro p _; rw [hzero]; rfl
  have h7 : NeutralOn (umamiCompose 1 (umamiCompose 1 1)) m := by
    intro p _; rw [hcube]; rfl
  intro hAtomic
  have hEq := hAtomic ⟨umamiCompose 1 (umamiCompose 1 1), h7⟩ ⟨(0 : ℕ), h0⟩
  simp only at hEq
  exact absurd hEq (by norm_num [umamiCompose])

/-! ## The clopen-ball interface, and its ternary instance -/

/-- Mirror of `ConstraintClopenRefinement.BTBranch`. -/
inductive BTBranch
  | negativeBranch | zeroBranch | positiveBranch
  deriving DecidableEq, Fintype, Repr

/-- The branch of a balanced-ternary digit. -/
def branchTrit : BTBranch → Trit
  | .negativeBranch => Trit.neg
  | .zeroBranch => Trit.zer
  | .positiveBranch => Trit.pos

/-- **The Agda branch type is the repository's balanced-ternary digit**, in the
enumeration order of both files. -/
def btBranchEquivTrit : BTBranch ≃ Trit where
  toFun := branchTrit
  invFun
    | Trit.neg => .negativeBranch
    | Trit.zer => .zeroBranch
    | Trit.pos => .positiveBranch
  left_inv := by intro b; cases b <;> rfl
  right_inv := by intro t; cases t <;> rfl

/-- Mirror of `ConstraintClopenRefinement.ClopenBallSystem`.  `ballOpen` and
`ballClosed` are the Agda's authority fields: they are unconstrained
`Set`-valued fields there, and unconstrained predicates here. -/
structure ClopenBallSystem where
  Point : Type
  Depth : Type
  nextDepth : Depth → Depth
  Ball : Depth → Point → Point → Prop
  ballOpen : Depth → Point → Prop
  ballClosed : Depth → Point → Prop
  childCentre : BTBranch → Depth → Point → Point
  childContained : ∀ (b : BTBranch) (d : Depth) (centre point : Point),
    Ball (nextDepth d) (childCentre b d centre) point → Ball d centre point
  childCover : ∀ (d : Depth) (centre point : Point),
    Ball d centre point → ∃ b : BTBranch, Ball (nextDepth d) (childCentre b d centre) point

/-- Ternary streams: the points of the instance. -/
abbrev TritStream := ℕ → Trit

/-- The depth-`d` ball around `c`: agreement on the first `d` digits. -/
def Cyl (d : ℕ) (c p : TritStream) : Prop := ∀ i, i < d → c i = p i

theorem cyl_refl (d : ℕ) (c : TritStream) : Cyl d c c := fun _ _ => rfl

theorem cyl_symm {d : ℕ} {c p : TritStream} (h : Cyl d c p) : Cyl d p c :=
  fun i hi => (h i hi).symm

theorem cyl_trans {d : ℕ} {a b c : TritStream} (hab : Cyl d a b) (hbc : Cyl d b c) :
    Cyl d a c := fun i hi => (hab i hi).trans (hbc i hi)

theorem cyl_succ_iff (d : ℕ) (c p : TritStream) :
    Cyl (d + 1) c p ↔ Cyl d c p ∧ c d = p d := by
  constructor
  · intro h
    exact ⟨fun i hi => h i (Nat.lt_succ_of_lt hi), h d (Nat.lt_succ_self d)⟩
  · rintro ⟨h, hd⟩ i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
    · exact h i hlt
    · subst heq; exact hd

/-- The centre of the child ball in a given branch: overwrite digit `d`. -/
def cylChildCentre (b : BTBranch) (d : ℕ) (c : TritStream) : TritStream :=
  Function.update c d (branchTrit b)

theorem cylChildCentre_apply_lt {b : BTBranch} {d i : ℕ} (c : TritStream) (h : i < d) :
    cylChildCentre b d c i = c i := by
  simp [cylChildCentre, Nat.ne_of_lt h]

@[simp] theorem cylChildCentre_apply_self (b : BTBranch) (d : ℕ) (c : TritStream) :
    cylChildCentre b d c d = branchTrit b := by
  simp [cylChildCentre]

/-- A child ball sits inside its parent. -/
theorem cyl_child_contained (b : BTBranch) (d : ℕ) (c p : TritStream)
    (h : Cyl (d + 1) (cylChildCentre b d c) p) : Cyl d c p := by
  intro i hi
  rw [← cylChildCentre_apply_lt (b := b) (d := d) c hi]
  exact h i (Nat.lt_succ_of_lt hi)

/-- The three children cover the parent. -/
theorem cyl_child_cover (d : ℕ) (c p : TritStream) (h : Cyl d c p) :
    ∃ b : BTBranch, Cyl (d + 1) (cylChildCentre b d c) p := by
  refine ⟨btBranchEquivTrit.symm (p d), ?_⟩
  rw [cyl_succ_iff]
  constructor
  · intro i hi
    rw [cylChildCentre_apply_lt _ hi]
    exact h i hi
  · rw [cylChildCentre_apply_self]
    exact btBranchEquivTrit.apply_symm_apply (p d)

/-- **A checked instance of the clopen-ball interface.**  The two substantive
side-conditions are theorems above; the two authority fields are filled with the
trivial predicate, which is exactly what the Agda record permits. -/
def ternaryBallSystem : ClopenBallSystem where
  Point := TritStream
  Depth := ℕ
  nextDepth d := d + 1
  Ball := Cyl
  ballOpen := fun _ _ => True
  ballClosed := fun _ _ => True
  childCentre := cylChildCentre
  childContained := cyl_child_contained
  childCover := cyl_child_cover

/-- Distinct branches give disjoint child balls. -/
theorem children_disjoint {b b' : BTBranch} (hbb : b ≠ b') (d : ℕ) (c p : TritStream)
    (hb : Cyl (d + 1) (cylChildCentre b d c) p) (hb' : Cyl (d + 1) (cylChildCentre b' d c) p) :
    False := by
  have h1 := ((cyl_succ_iff _ _ _).mp hb).2
  have h2 := ((cyl_succ_iff _ _ _).mp hb').2
  rw [cylChildCentre_apply_self] at h1 h2
  exact hbb (btBranchEquivTrit.injective (h1.trans h2.symm))

/-- **No ball is atomic.**  Every ball contains points lying in three different
child balls; in particular the coarse ball does not determine the fine one.
This is the content the Agda records as the `Bool` field
`publicZeroIsAtomic ≡ false`. -/
theorem no_atomic_ball (d : ℕ) (c : TritStream) :
    ∃ p q : TritStream, Cyl d c p ∧ Cyl d c q ∧ p d ≠ q d := by
  refine ⟨Function.update c d Trit.neg, Function.update c d Trit.pos, ?_, ?_, ?_⟩
  · intro i hi; simp [Nat.ne_of_lt hi]
  · intro i hi; simp [Nat.ne_of_lt hi]
  · simp

/-- Each of the three child balls of a ball is inhabited. -/
theorem child_inhabited (b : BTBranch) (d : ℕ) (c : TritStream) :
    ∃ p : TritStream, Cyl (d + 1) (cylChildCentre b d c) p ∧ Cyl d c p :=
  ⟨cylChildCentre b d c, cyl_refl _ _,
    cyl_child_contained b d c _ (cyl_refl _ _)⟩

/-- **Clopenness, combinatorially**: the complement of a ball is a union of
balls of the same depth — a point outside a ball has a whole ball around it
still outside. -/
theorem ball_complement_union {d : ℕ} {c p : TritStream} (h : ¬ Cyl d c p) :
    ∀ q, Cyl d p q → ¬ Cyl d c q :=
  fun _ hpq hcq => h (cyl_trans hcq (cyl_symm hpq))

/-! ## The cuisine transport as a depth-15 ball projection -/

/-- The ternary stream of a cuisine intensity: its hyperfabric shadow in the
fixed enumeration of the supersingular base, padded with the neutral digit. -/
noncomputable def intensityStream (u : ℕ) : TritStream := fun i =>
  if h : i < 15 then umamiFabric u (sspEquivFin15.symm ⟨i, h⟩) else Trit.neg

/-- **The cuisine transport is exactly the depth-15 ball projection.**  Two
blends have the same hyperfabric shadow precisely when their ternary streams
agree to depth fifteen, i.e. lie in a common depth-15 clopen ball. -/
theorem umamiFabric_eq_iff_ball (a b : ℕ) :
    umamiFabric a = umamiFabric b ↔ Cyl 15 (intensityStream a) (intensityStream b) := by
  constructor
  · intro h i hi
    simp [intensityStream, hi, h]
  · intro h
    funext p
    have hp : (sspEquivFin15 p : ℕ) < 15 := (sspEquivFin15 p).isLt
    have := h (sspEquivFin15 p) hp
    simpa [intensityStream, hp, Fin.eta] using this

/-- Seasoning a blend with two further copies of itself lands in the neutral
shadow: the cube law of `Cuisine.UmamiTransport`, read as a ball statement. -/
theorem cube_in_neutral_ball (u : ℕ) :
    Cyl 15 (intensityStream (umamiCompose u (umamiCompose u u))) (intensityStream 0) := by
  rw [← umamiFabric_eq_iff_ball]
  rw [umamiFabric_cube]
  have : umamiFabric 0 = fabricZero := by
    apply fabricZMod.injective
    rw [fabricZMod_umamiFabric, fabricZMod_zero]
    funext p
    simp [toneAt]
  rw [this]

/-- **The cuisine supervoxel is not atomic.**  There are distinct cuisine
intensities in one depth-15 ball, so the transport genuinely forgets
information — the honest form of the Agda's
`SamePublicZeroDifferentDynamics`. -/
theorem cuisine_supervoxel_not_atomic :
    ∃ a b : ℕ, a ≠ b ∧ Cyl 15 (intensityStream a) (intensityStream b) := by
  refine ⟨umamiCompose 1 (umamiCompose 1 1), 0, by decide, ?_⟩
  exact cube_in_neutral_ball 1

end Cuisine.SupervoxelClopen
