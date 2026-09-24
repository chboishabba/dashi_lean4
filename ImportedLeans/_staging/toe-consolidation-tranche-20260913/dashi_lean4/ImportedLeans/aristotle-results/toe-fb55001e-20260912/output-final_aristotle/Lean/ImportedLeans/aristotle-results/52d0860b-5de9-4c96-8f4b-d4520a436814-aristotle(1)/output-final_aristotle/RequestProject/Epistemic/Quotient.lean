import RequestProject.Epistemic.Observer

/-!
# Sections, residuals and exact reopening

A projection `Fine → Coarse` throws information away.  Two different repairs are
available, and they are *not* equivalent:

* a **section** picks one representative per coarse value.  That is enough to
  reconstruct every fibre-constant observable (`fibreConstant_eq_pullback`), and
  provably not enough to reconstruct the fine state itself
  (`exists_section_not_injective`);
* a **residual coordinate** records exactly what the projection forgot.  With it,
  reopening is exact (`ExactRecoverable`), surface plus residual determines the
  fine state (`ExactRecoverable.eq_of_project_eq_of_residual_eq`), and therefore
  any motion hidden by the projection must move the residual
  (`ExactRecoverable.residual_ne_of_hiddenTransition`).

Residual coordinates compose: refining a projection in two stages gives a total
residual which is the *product* of the two stage residuals
(`ExactRecoverable.comp_residual_eq`), so a quotient tower does not need one
ever-widening public record.

The module closes with the predicate lattice: coarse predicates pull back to
fibre-constant fine predicates, and the pullback preserves meet and join.
-/

namespace Epistemic

variable {Fine Coarse Value : Type}

/-! ## Fibre-constant observables and sections -/

/-- An observable that cannot distinguish states inside a fibre. -/
def FibreConstant (proj : Fine → Coarse) (obs : Fine → Value) : Prop :=
  ∀ x y, proj x = proj y → obs x = obs y

/-- Reading a coarse observable upstairs. -/
def pullbackObs (proj : Fine → Coarse) (obs : Coarse → Value) : Fine → Value :=
  fun x => obs (proj x)

theorem fibreConstant_pullbackObs (proj : Fine → Coarse) (obs : Coarse → Value) :
    FibreConstant proj (pullbackObs proj obs) := fun _ _ h => congrArg obs h

/-- A projection together with a choice of representative for each coarse value. -/
structure SectionedProjection (Fine Coarse : Type) where
  /-- The projection. -/
  project : Fine → Coarse
  /-- A chosen representative of each coarse value. -/
  representative : Coarse → Fine
  /-- The representative really projects to its value. -/
  section_eq : ∀ c, project (representative c) = c

namespace SectionedProjection

variable (s : SectionedProjection Fine Coarse)

/-- Reading a fine observable at the chosen representatives. -/
def representativeObs (obs : Fine → Value) : Coarse → Value :=
  fun c => obs (s.representative c)

/-- **A section reconstructs every fibre-constant observable.** -/
theorem fibreConstant_eq_pullback {obs : Fine → Value}
    (h : FibreConstant s.project obs) (x : Fine) :
    obs x = pullbackObs s.project (s.representativeObs obs) x :=
  h x (s.representative (s.project x)) (s.section_eq (s.project x)).symm

/-- The projection of a sectioned projection is surjective. -/
theorem project_surjective : Function.Surjective s.project :=
  fun c => ⟨s.representative c, s.section_eq c⟩

end SectionedProjection

/-- **A section alone does not reconstruct fine states**: there is a sectioned
projection whose projection is not injective. -/
theorem exists_section_not_injective :
    ∃ s : SectionedProjection Bool Unit, ¬ Function.Injective s.project :=
  ⟨⟨fun _ => (), fun _ => true, fun _ => rfl⟩, fun h => by simpa using h (a₁ := false) (a₂ := true) rfl⟩

/-! ## Exact reopening from a residual coordinate -/

/-- A projection with an explicit residual coordinate that makes reopening exact:
the coarse value together with the residual reconstructs the fine state on the
nose. -/
structure ExactRecoverable (Fine Coarse : Type) : Type 1 where
  /-- The forgotten coordinate. -/
  Residual : Type
  /-- The projection to the public surface. -/
  project : Fine → Coarse
  /-- The residual of a fine state. -/
  residual : Fine → Residual
  /-- Reopening a surface value along a residual. -/
  reopen : Coarse → Residual → Fine
  /-- Reopening is exact. -/
  reopen_exact : ∀ x, reopen (project x) (residual x) = x

namespace ExactRecoverable

variable (r : ExactRecoverable Fine Coarse)

/-- **Surface plus residual determines the fine state.** -/
theorem eq_of_project_eq_of_residual_eq {x y : Fine} (hp : r.project x = r.project y)
    (hr : r.residual x = r.residual y) : x = y := by
  have := r.reopen_exact x
  rw [hp, hr, r.reopen_exact y] at this
  exact this.symm

/-- The pair (surface, residual) is a separating observer. -/
theorem separating_pair : Separating (pairObserver r.project r.residual) := by
  intro x y h
  exact r.eq_of_project_eq_of_residual_eq (congrArg Prod.fst h) (congrArg Prod.snd h)

/-- **Every motion hidden by the projection must move the residual.** -/
theorem residual_ne_of_hiddenTransition {f : Fine → Fine} {x : Fine}
    (h : HiddenTransition r.project f x) : r.residual (f x) ≠ r.residual x :=
  fun hres => h.1 (r.eq_of_project_eq_of_residual_eq h.2 hres)

/-- The residual is itself a fine observable; it is fibre-constant only in the
degenerate case where the projection is already separating. -/
theorem separating_project_of_fibreConstant_residual
    (h : FibreConstant r.project r.residual) : Separating r.project :=
  fun x y hxy => r.eq_of_project_eq_of_residual_eq hxy (h x y hxy)

/-- Composing two exactly recoverable projections; the residual of the composite is
the product of the stage residuals. -/
def comp {Mid : Type} (first : ExactRecoverable Fine Mid)
    (second : ExactRecoverable Mid Coarse) : ExactRecoverable Fine Coarse where
  Residual := first.Residual × second.Residual
  project := fun x => second.project (first.project x)
  residual := fun x => (first.residual x, second.residual (first.project x))
  reopen := fun c p => first.reopen (second.reopen c p.2) p.1
  reopen_exact := by
    intro x
    simp only [second.reopen_exact (first.project x), first.reopen_exact x]

/-- **The composite residual factors by stage.** -/
theorem comp_residual_eq {Mid : Type} (first : ExactRecoverable Fine Mid)
    (second : ExactRecoverable Mid Coarse) :
    (comp first second).Residual = (first.Residual × second.Residual) := rfl

end ExactRecoverable

/-! ## The predicate lattice over a projection -/

/-- A boolean predicate on a carrier. -/
abbrev Predicate (α : Type) := α → Bool

/-- Pointwise meet of predicates. -/
def Predicate.meet {α : Type} (p q : Predicate α) : Predicate α := fun x => p x && q x

/-- Pointwise join of predicates. -/
def Predicate.join {α : Type} (p q : Predicate α) : Predicate α := fun x => p x || q x

/-- Reading a coarse predicate upstairs. -/
def pullbackPred (proj : Fine → Coarse) (p : Predicate Coarse) : Predicate Fine :=
  fun x => p (proj x)

/-- A predicate that cannot distinguish states inside a fibre. -/
def FibreConstantPred (proj : Fine → Coarse) (p : Predicate Fine) : Prop :=
  ∀ x y, proj x = proj y → p x = p y

/-- **Coarse predicates pull back to fibre-constant fine predicates.** -/
theorem fibreConstantPred_pullback (proj : Fine → Coarse) (p : Predicate Coarse) :
    FibreConstantPred proj (pullbackPred proj p) := fun _ _ h => congrArg p h

theorem pullbackPred_meet (proj : Fine → Coarse) (p q : Predicate Coarse) :
    pullbackPred proj (Predicate.meet p q) =
      Predicate.meet (pullbackPred proj p) (pullbackPred proj q) := rfl

theorem pullbackPred_join (proj : Fine → Coarse) (p q : Predicate Coarse) :
    pullbackPred proj (Predicate.join p q) =
      Predicate.join (pullbackPred proj p) (pullbackPred proj q) := rfl

/-- A section reconstructs every fibre-constant predicate. -/
theorem SectionedProjection.fibreConstantPred_eq_pullback (s : SectionedProjection Fine Coarse)
    {p : Predicate Fine} (h : FibreConstantPred s.project p) (x : Fine) :
    p x = pullbackPred s.project (fun c => p (s.representative c)) x :=
  h x (s.representative (s.project x)) (s.section_eq (s.project x)).symm

/-! ## Non-factorability

A decision procedure on fine states factors through the projection when the
coarse value alone already determines it.  A single collision on which the
procedure disagrees rules out *every* such factorisation. -/

/-- The fine-state function is already determined by the coarse surface. -/
def FactorsThrough {Route : Type} (proj : Fine → Coarse) (route : Fine → Route) : Prop :=
  ∃ interpret : Coarse → Route, ∀ x, route x = interpret (proj x)

theorem factorsThrough_iff_fibreConstant {Route : Type} (proj : Fine → Coarse)
    (route : Fine → Route) (s : SectionedProjection Fine Coarse)
    (hproj : s.project = proj) :
    FactorsThrough proj route ↔ FibreConstant proj route := by
  subst hproj
  constructor
  · rintro ⟨interpret, h⟩ x y hxy
    rw [h x, h y, hxy]
  · intro h
    exact ⟨fun c => route (s.representative c), fun x =>
      h x (s.representative (s.project x)) (s.section_eq (s.project x)).symm⟩

/-- **A collision on which the routes differ rules out every factorisation.** -/
theorem not_factorsThrough {Route : Type} {proj : Fine → Coarse} {route : Fine → Route}
    {x y : Fine} (hproj : proj x = proj y) (hroute : route x ≠ route y) :
    ¬ FactorsThrough proj route := by
  rintro ⟨interpret, h⟩
  exact hroute (by rw [h x, h y, hproj])

end Epistemic
