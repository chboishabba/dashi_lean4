import Integration.CoordinateSufficiency

/-!
# Context-indexed roles, and the corpus's own non-factorability owner

`Agda/DASHI/Core/IntersectionalNonFactorability.agda` is already a
domain-neutral module: it defines a `FactorsThrough` record, a
`NonFactorabilityWitness` record (a collided pair the consumer separates), and
proves `witnessRulesOutEveryFlatFactorisation` — a witness refutes every
factorisation.  That is precisely
`Integration.CoordinateSufficiency.Determines` and
`not_determines_of_collision`.

This file records the identification rather than duplicating it, and then adds
the two theorem shapes that several lanes need and none of them owns.

Contents.

* `FactorsThrough`, `NonFactorabilityWitness`, `witness_rules_out_every_factorisation`
  — the Agda records and theorem, mirrored;
* `factorsThrough_iff_determines` — **the identification**: the Agda record is
  inhabited exactly when the Lean owner's `Determines` holds.  So the corpus
  module and the owner are the same notion, and the domain modules supply
  witnesses rather than re-deriving the theory;
* `flat_reweighting_cannot_repair` — the Agda module's own concrete witness,
  mirrored;
* `not_determines_of_downstream` — **downstream recharting cannot repair an
  upstream erasure**: if a consumer does not factor through an observation, it
  does not factor through any further processing of it either.  This is the
  general form of the strengthening several lanes state separately;
* `ContextEliminable`, `context_not_eliminable_of_split`,
  `contextEliminable_iff_not_essential` — **failure of context elimination**: a
  role assignment indexed by a frame need not come from any frame-free
  assignment, and that is exactly essentiality of the frame coordinate;
* `roleIn`, `role_not_context_free` — a two-frame instance;
* `realizedAccess` — a five-coordinate product consumer with **every**
  coordinate essential, so its only sufficient coordinate set is everything
  (`access_only_full_is_sufficient`), together with
  `access_pair_not_separable`: two of the coordinates genuinely interact rather
  than contributing independently.

The carriers are two-element label types and Boolean products.  Nothing here is
a claim about people, institutions, social structure or any empirical outcome:
the theorems are about projections of product states, and the domain reading of
the coordinates is supplied elsewhere.
-/

namespace Integration.ContextIndexedRole

open Integration.CoordinateSufficiency

/-! ## The corpus's own owner -/

variable {Situated Flat Outcome : Type}

/-- Mirror of the Agda `FactorsThrough` record. -/
structure FactorsThrough (flatten : Situated → Flat) (phenomenon : Situated → Outcome) where
  /-- The claimed reading of the flat projection. -/
  interpretFlat : Flat → Outcome
  /-- The claimed factorisation. -/
  factorisation : ∀ s, phenomenon s = interpretFlat (flatten s)

/-- Mirror of the Agda `NonFactorabilityWitness` record. -/
structure NonFactorabilityWitness (flatten : Situated → Flat)
    (phenomenon : Situated → Outcome) where
  /-- The first situated state. -/
  left : Situated
  /-- The second. -/
  right : Situated
  /-- They have the same flat projection. -/
  sameFlatProjection : flatten left = flatten right
  /-- But different outcomes. -/
  situatedOutcomesDiffer : phenomenon left ≠ phenomenon right

/-- Mirror of the Agda `witnessRulesOutEveryFlatFactorisation`. -/
theorem witness_rules_out_every_factorisation {flatten : Situated → Flat}
    {phenomenon : Situated → Outcome} (w : NonFactorabilityWitness flatten phenomenon)
    (f : FactorsThrough flatten phenomenon) : False :=
  w.situatedOutcomesDiffer <| by
    rw [f.factorisation w.left, f.factorisation w.right, w.sameFlatProjection]

/-- **The identification.**  The Agda record is inhabited exactly when the Lean
owner's `Determines` holds, so the corpus module is that owner under another
name.  (The `Nonempty` hypothesis only names a value off the image.) -/
theorem factorsThrough_iff_determines [Nonempty Outcome] (flatten : Situated → Flat)
    (phenomenon : Situated → Outcome) :
    Nonempty (FactorsThrough flatten phenomenon) ↔ Determines flatten phenomenon := by
  constructor
  · rintro ⟨f⟩ x y hxy
    rw [f.factorisation x, f.factorisation y, hxy]
  · intro h
    obtain ⟨g, hg⟩ := (determines_iff_refines flatten phenomenon).mp h
    exact ⟨⟨g, hg⟩⟩

/-- A witness is exactly a refutation of determination. -/
theorem determines_false_of_witness {flatten : Situated → Flat}
    {phenomenon : Situated → Outcome} (w : NonFactorabilityWitness flatten phenomenon) :
    ¬ Determines flatten phenomenon :=
  not_determines_of_collision w.sameFlatProjection w.situatedOutcomesDiffer

/-! ### The module's own witness -/

/-- Mirror of the Agda `SituatedState`: two states sharing one flat label. -/
inductive SituatedState
  | sameLabelLowPower | sameLabelHighPower
  deriving DecidableEq, Repr, Fintype

/-- Mirror of the Agda `FlatSingleAxis`: a one-element carrier. -/
inductive FlatSingleAxis
  | sameLabel
  deriving DecidableEq, Repr, Fintype

/-- Mirror of `flatProjection`. -/
def flatProjection : SituatedState → FlatSingleAxis := fun _ => .sameLabel

/-- Mirror of `relationalOutcome`. -/
def relationalOutcome : SituatedState → Bool
  | .sameLabelLowPower => false
  | .sameLabelHighPower => true

/-- Mirror of `canonicalIntersectionalNonFactorability`. -/
def canonicalWitness : NonFactorabilityWitness flatProjection relationalOutcome where
  left := .sameLabelLowPower
  right := .sameLabelHighPower
  sameFlatProjection := rfl
  situatedOutcomesDiffer := by decide

/-- Mirror of `flatReweightingCannotRepairMissingRelation`: **no** reading of the
flat projection returns the outcome. -/
theorem flat_reweighting_cannot_repair : ¬ Determines flatProjection relationalOutcome :=
  determines_false_of_witness canonicalWitness

/-! ## Downstream recharting cannot repair an upstream erasure -/

variable {X Y Z W : Type}

/-- **The general strengthening.**  If a consumer does not factor through an
observation, it does not factor through any further processing of that
observation either: post-processing only ever loses more. -/
theorem not_determines_of_downstream {O : X → Y} {C : X → Z} (g : Y → W)
    (h : ¬ Determines O C) : ¬ Determines (fun x => g (O x)) C := by
  intro hg
  exact h fun x y hxy => hg x y (congrArg g hxy)

/-- The positive companion: a coarser observation is determined by the finer
one, so the information order is respected. -/
theorem determines_of_upstream {O : X → Y} {C : X → Z} (g : Y → W)
    (h : Determines (fun x => g (O x)) C) : Determines O C :=
  fun x y hxy => h x y (congrArg g hxy)

/-! ## Failure of context elimination -/

variable {Frame Entity Role : Type}

/-- A context-indexed role assignment **can be eliminated** when some frame-free
assignment reproduces it. -/
def ContextEliminable (roleIn : Frame → Entity → Role) : Prop :=
  ∃ r : Entity → Role, ∀ f e, roleIn f e = r e

/-- **Context cannot be eliminated** as soon as two frames disagree about one
entity. -/
theorem context_not_eliminable_of_split {roleIn : Frame → Entity → Role} {f₁ f₂ : Frame}
    {e : Entity} (h : roleIn f₁ e ≠ roleIn f₂ e) : ¬ ContextEliminable roleIn := by
  rintro ⟨r, hr⟩
  exact h (by rw [hr f₁ e, hr f₂ e])

/-- And eliminability is exactly non-essentiality of the frame coordinate of the
product `Frame × Entity`, so this is the coordinate owner again. -/
theorem contextEliminable_iff_not_essential [Nonempty Frame] (roleIn : Frame → Entity → Role) :
    ContextEliminable roleIn ↔
      ∀ f₁ f₂ : Frame, ∀ e : Entity, roleIn f₁ e = roleIn f₂ e := by
  constructor
  · rintro ⟨r, hr⟩ f₁ f₂ e
    rw [hr f₁ e, hr f₂ e]
  · intro h
    exact ⟨fun e => roleIn (Classical.arbitrary Frame) e, fun f e => h f _ e⟩

/-- A two-frame, one-entity instance. -/
def roleIn : Bool → Unit → Bool := fun f _ => f

/-- **The role is genuinely context-indexed**: no frame-free assignment
reproduces it. -/
theorem role_not_context_free : ¬ ContextEliminable roleIn :=
  context_not_eliminable_of_split (f₁ := true) (f₂ := false) (e := ())
    (by simp [roleIn])

/-! ## A relational product consumer -/

/-- A five-coordinate Boolean product with an outcome that needs all of it: the
first two coordinates must hold together, or else the last three must. -/
def realizedAccess (x : Fin 5 → Bool) : Bool :=
  (x 0 && x 1) || (x 2 && x 3 && x 4)

/-- **Every coordinate is essential.** -/
theorem access_all_essential (j : Fin 5) :
    Essential (A := fun _ : Fin 5 => Bool) j realizedAccess := by
  fin_cases j
  · exact ⟨![true, true, false, false, false], ![false, true, false, false, false],
      by intro i hi; fin_cases i <;> simp_all, by decide⟩
  · exact ⟨![true, true, false, false, false], ![true, false, false, false, false],
      by intro i hi; fin_cases i <;> simp_all, by decide⟩
  · exact ⟨![false, false, true, true, true], ![false, false, false, true, true],
      by intro i hi; fin_cases i <;> simp_all, by decide⟩
  · exact ⟨![false, false, true, true, true], ![false, false, true, false, true],
      by intro i hi; fin_cases i <;> simp_all, by decide⟩
  · exact ⟨![false, false, true, true, true], ![false, false, true, true, false],
      by intro i hi; fin_cases i <;> simp_all, by decide⟩

/-- Hence the essential set is everything… -/
theorem access_essentialSet_univ :
    essentialSet (A := fun _ : Fin 5 => Bool) realizedAccess = Set.univ :=
  Set.eq_univ_of_forall access_all_essential

/-- …and **the only sufficient coordinate set is the whole product**: dropping
any single coordinate loses the outcome. -/
theorem access_only_full_is_sufficient (S : Set (Fin 5)) :
    FactorsOn (A := fun _ : Fin 5 => Bool) S realizedAccess ↔ S = Set.univ := by
  rw [factorsOn_iff_essentialSet_subset, access_essentialSet_univ]
  exact ⟨fun h => Set.eq_univ_of_univ_subset h, fun h => h ▸ subset_rfl⟩

/-- The joint contribution of the first two coordinates, valued in `ℤ`. -/
def accessValue (a b : Bool) : ℤ := if a && b then 1 else 0

/-- **The first two coordinates interact.**  Their joint contribution is not a
sum of separate contributions, so "both coordinates matter" understates the
situation: no coordinatewise decomposition exists at all. -/
theorem access_pair_not_separable : ¬ Separable accessValue := by
  intro h
  have := separable_rectangle h true false true false
  simp [accessValue] at this

/-- And that joint contribution really is the restriction of the product
consumer to its first two coordinates. -/
theorem accessValue_eq_restriction (a b : Bool) :
    (if realizedAccess ![a, b, false, false, false] then (1 : ℤ) else 0) = accessValue a b := by
  cases a <;> cases b <;> simp [realizedAccess, accessValue]

end Integration.ContextIndexedRole
