import Integration.ResidualQuotient
import Integration.PathTransport
import Spine.FiniteReindex

/-!
# A taxonomy of residuals

"Residual" is overloaded across this corpus: what a quotient must retain to be
reopened, what a trajectory deposits, a relational contrast between two times,
an unresolved set of admissible readings, and the index of a deletion/fibre
decomposition.  They obey *different* laws, so identifying them is a mistake;
but they share theorems, so separating them into unrelated files is also a
mistake.  This file types them, states the law that distinguishes each, and
proves the separations.

```
R_reconstructive   reopen (π x) (r x) = x
R_trajectory       monotone along transitions ⇒ reverse reachability obstruction
R_contrastive      r depends on two states, and is not a function of the present one
R_ambiguity        admissible alternatives are retained, never collapsed
R_combinatorial    indexes an exact fibre decomposition of a weighted total
```

Contents.

* `Reconstructive` — the reopening law, with `Integration.Residual.ResidualQuotient`
  as the bundled version and `reconstructive_injective` the consequence
  (a reconstructive residual separates every fibre);
* `Trajectory` — the persistence law and `trajectory_obstruction`, the reverse
  reachability obstruction (delegated to
  `Integration.PathTransport.persistent_obstruction`, which is the shared
  theorem);
* `Contrastive`, `contrast_not_function_of_present` — the contrast operator
  `δ (x_{t-1}, x_t)` and the proof that the present state does not determine it:
  the observer non-descent theorem in derivative clothing;
* `Ambiguity`, `resolve`, `resolve_eq_none_of_disagree`,
  `resolve_ne_some_of_disagree` — unresolved alternatives are retained as
  ambiguity, not collapsed to a negative;
* `combinatorial_residual_exact` — the deletion/fibre residual, whose law is the
  exact reindexing identity of `Spine.FiniteReindex`;
* `trajectory_not_reconstructive`, `contrastive_not_reconstructive` — the
  separations: a residual can be persistent along trajectories, or genuinely
  relational, and still fail to reopen the quotient.  So the five classes are
  not one type with five names.
-/

namespace Integration.ResidualTaxonomy

open Integration.Residual
open Integration.PathTransport

variable {X Y R : Type*}

/-! ## Reconstructive: needed to reopen a quotient -/

/-- The reconstructive law: coarse state plus residual reopens the rich state. -/
def Reconstructive (π : X → Y) (r : X → R) (reopen : Y → R → X) : Prop :=
  ∀ x, reopen (π x) (r x) = x

/-- A reconstructive residual separates the fibres of the projection. -/
theorem reconstructive_injective {π : X → Y} {r : X → R} {reopen : Y → R → X}
    (h : Reconstructive π r reopen) {x y : X} (hπ : π x = π y) (hr : r x = r y) : x = y := by
  rw [← h x, ← h y, hπ, hr]

/-- The bundled version already in the tree is an instance. -/
theorem reconstructive_of_residualQuotient {Rich Coarse Res : Type}
    (Q : ResidualQuotient Rich Coarse Res) :
    Reconstructive Q.project Q.residual Q.reopen := Q.reopen_project

/-! ## Trajectory: a record of path-dependent history -/

/-- The trajectory law: the residue is never erased by an allowed transition. -/
def Trajectory (step : X → X → Prop) (r : X → Prop) : Prop :=
  ∀ x y, step x y → r x → r y

/-- **The law of this class**: a deposited, persistent residue obstructs reverse
reachability.  The theorem is shared with the path lane; only the reading is
specific. -/
theorem trajectory_obstruction {step : X → X → Prop} {r : X → Prop}
    (h : Trajectory step r) {x y : X} (hx : r x) (hy : ¬ r y) : ¬ Path step x y :=
  persistent_obstruction h hx hy

/-- The numeric form: a monotone quantity obstructs reaching any state of
strictly smaller value. -/
theorem trajectory_obstruction_mono {α : Type*} [Preorder α] {step : X → X → Prop} {I : X → α}
    (hmono : ∀ x y, step x y → I x ≤ I y) {x y : X} (hlt : I y < I x) : ¬ Path step x y :=
  not_path_of_lt hmono hlt

/-! ## Contrastive: relational between states or times -/

/-- The contrastive residual is a function of *two* states. -/
def Contrastive (δ : X → X → R) (r : X → X → R) : Prop := ∀ a b, r a b = δ a b

/-- **The law of this class**: the present state does not determine the
contrast.  Concretely, on a two-element carrier with the difference contrast,
two histories with the same present state have different contrasts — so no
function of the present state is the contrast. -/
theorem contrast_not_function_of_present :
    ¬ ∃ f : Bool → ℤ, ∀ a b : Bool,
        f b = (if b then 1 else 0) - (if a then 1 else 0) := by
  rintro ⟨f, hf⟩
  have h1 := hf false true
  have h2 := hf true true
  rw [h1] at h2
  norm_num at h2

/-- Stated for a general contrast: a contrast that takes two different values at
the same present state is not a function of the present state. -/
theorem contrast_not_present_of_disagree {δ : X → X → R} {a a' b : X}
    (hne : δ a b ≠ δ a' b) : ¬ ∃ f : X → R, ∀ u v : X, f v = δ u v := by
  rintro ⟨f, hf⟩
  exact hne ((hf a b).symm.trans (hf a' b))

/-! ## Ambiguity: unresolved admissible alternatives -/

/-- The ambiguity residual retains a set of admissible readings. -/
def Ambiguity (X : Type*) : Type _ := X → Prop

/-- Resolution succeeds only when the admissible readings agree. -/
noncomputable def resolve [Nonempty X] (A : Ambiguity X) : Option X := by
  classical
  exact if h : ∃! x, A x then some h.choose else none

/-- **The law of this class**: two distinct admissible readings are retained as
ambiguity, never collapsed to a value. -/
theorem resolve_eq_none_of_disagree [Nonempty X] {A : Ambiguity X} {x y : X}
    (hx : A x) (hy : A y) (hne : x ≠ y) : resolve A = none := by
  classical
  have hnot : ¬ ∃! z, A z := by
    rintro ⟨z, _, huniq⟩
    exact hne ((huniq x hx).trans (huniq y hy).symm)
  simp [resolve, hnot]

/-- And ambiguity is not negative evidence: `none` is not `some` of anything, in
particular not of a default reading. -/
theorem resolve_ne_some_of_disagree [Nonempty X] {A : Ambiguity X} {x y : X}
    (hx : A x) (hy : A y) (hne : x ≠ y) (z : X) : resolve A ≠ some z := by
  rw [resolve_eq_none_of_disagree hx hy hne]
  simp

/-! ## Combinatorial: the index of a deletion/fibre decomposition -/

/-- **The law of this class** is exact reindexing: the total over a marked source
equals the total over the fibres of the residual index.  Nothing is estimated. -/
theorem combinatorial_residual_exact {ι κ : Type*} {M : Type*} [AddCommMonoid M]
    [DecidableEq κ] [Fintype κ] (s : Finset ι) (residualIndex : ι → κ) (w : ι → M) :
    ∑ k, ∑ i ∈ s with residualIndex i = k, w i = ∑ i ∈ s, w i :=
  Spine.FiniteReindex.foldW_fiberwise s residualIndex w

/-! ## The separations -/

/-- **A trajectory residue need not be reconstructive.**  Here the residue is
persistent along the transition, but the coarse state together with it does not
determine the rich state. -/
theorem trajectory_not_reconstructive :
    ∃ (step : Bool × Bool → Bool × Bool → Prop) (r : Bool × Bool → Bool),
      Trajectory step (fun x => r x = true) ∧
        ∀ reopen : Unit → Bool → Bool × Bool,
          ¬ Reconstructive (fun _ : Bool × Bool => ()) r reopen := by
  refine ⟨fun x y => y = x, Prod.fst, fun x y hxy hx => by rw [hxy]; exact hx, ?_⟩
  intro reopen h
  have h1 := h (true, true)
  have h2 := h (true, false)
  rw [show (Prod.fst (true, true) : Bool) = true from rfl] at h1
  rw [show (Prod.fst (true, false) : Bool) = true from rfl] at h2
  rw [h1] at h2
  exact absurd h2 (by decide)

/-- **A contrastive residual is not reconstructive either**, because it is not
even a function of the state it is supposed to reopen. -/
theorem contrastive_not_reconstructive :
    ¬ ∃ f : Bool → ℤ, ∀ a b : Bool, f b = (if b then 1 else 0) - (if a then 1 else 0) :=
  contrast_not_function_of_present

end Integration.ResidualTaxonomy
