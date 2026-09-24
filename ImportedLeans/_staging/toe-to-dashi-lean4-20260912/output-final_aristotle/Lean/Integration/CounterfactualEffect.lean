import Integration.CoordinateSufficiency

/-!
# Interventions, responses, and why a label is not an effect

Many lanes of the corpus need the same three-part apparatus: a state, an
*action* that changes the state, and an *observation* that reports on it.  The
quantity of interest is then a contrast between what is observed before and
after.  Written domain-neutrally this is one object, and the two theorems worth
owning are the ones that keep being re-derived under different names:

* an **intervention label does not determine its effect**, because the effect is
  a function of the situated state and not of the label; and
* **observation is not intervention**: two states an observation identifies need
  not stay identified after the action, so no amount of observational
  resolution licenses a post-intervention conclusion.

Both are instances of `Integration.CoordinateSufficiency.Determines` failing,
which is the point: they are not a separate causal calculus.

## Contents

### The generic owner

* `Response` — the pair (before, after) of observations;
* `contrast` — their difference, where the observation is group-valued;
* `Homogeneous` — the effect is the same at every state;
* `contrast_not_homogeneous` — an explicit action whose contrast varies, so the
  action alone does not name an effect;
* `label_not_determines_effect` — the coordinate form: an effect depending on a
  hidden coordinate is not determined by the label coordinate;
* `observation_not_intervention` — an observation that identifies two states
  which the action then separates, and the resulting refutation
  `not_determines_post_of_pre`;
* `intervention_can_reverse_ordering` — and the sharper version: the action can
  reverse the observed order of two states, so even a monotone reading of the
  observation transfers nothing across the action.

### The corpus instance

`Agda/DASHI/Education/EarlyLearningCounterfactualHeterogeneityExact.agda`
declares a three-coordinate `SituatedExposure` (intervention label, observed
position, hidden counterfactual), an effect direction, and the claim that the
label does not determine the effect.  Its Agda clauses for
`counterfactualRelativeEffect` are written against two *defined names* rather
than constructors; the Lean version below therefore defines the effect by
constructor patterns on the hidden coordinate, which is the reading the module's
own header and its downstream lemmas require.  (No Agda checker was run here, so
nothing is asserted about whether the Agda text elaborates.)

With that definition the intended results are proved, and three more are added:

* `counterfactual_determines_effect` — the hidden coordinate *is* sufficient;
* `effect_essential_set` — it is the only essential coordinate, so the label and
  the observed position are both inessential;
* `observed_group_cannot_determine_individual_effect` — the module's second
  witness, re-proved from the generic owner.

Nothing here is a claim about childcare, education, policy or any population.
The carriers are one-, two- and two-element label types.
-/

namespace Integration.CounterfactualEffect

open Integration.CoordinateSufficiency

/-! ## The generic intervention layer -/

section Generic

variable {X Y : Type}

/-- What an experiment reports: the observation before the action and after
it. -/
def Response (O : X → Y) (act : X → X) (x : X) : Y × Y := (O x, O (act x))

/-- The effect is **homogeneous** when the response is the same everywhere. -/
def Homogeneous (O : X → Y) (act : X → X) : Prop := ∀ x y, Response O act x = Response O act y

/-- The contrast, where the observation lands in an additive group. -/
def contrast {A : Type} [AddCommGroup A] (O : X → A) (act : X → X) (x : X) : A :=
  O (act x) - O x

/-- **Observation is not intervention.**  Two states the observation identifies
are separated by the action, so the pre-intervention observation does not
determine the post-intervention one. -/
theorem not_determines_post_of_pre {O : X → Y} {act : X → X} {x₁ x₂ : X}
    (hcoll : O x₁ = O x₂) (hsplit : O (act x₁) ≠ O (act x₂)) :
    ¬ Determines O (fun x => O (act x)) :=
  not_determines_of_collision hcoll hsplit

/-- The same hypotheses refute homogeneity of the response. -/
theorem not_homogeneous_of_split {O : X → Y} {act : X → X} {x₁ x₂ : X}
    (hsplit : O (act x₁) ≠ O (act x₂)) : ¬ Homogeneous O act := by
  intro h
  exact hsplit (congrArg Prod.snd (h x₁ x₂))

end Generic

/-! ### Explicit witnesses on `ℤ × ℤ` -/

/-- A state carrying a visible level and a hidden susceptibility. -/
abbrev Situated : Type := ℤ × ℤ

/-- The observation reports only the visible level. -/
def level (s : Situated) : ℤ := s.1

/-- The action adds the hidden susceptibility to the visible level. -/
def treat (s : Situated) : Situated := (s.1 + s.2, s.2)

/-- **The contrast is exactly the hidden coordinate**, so the action does not
name a number: it names a function of the state. -/
theorem contrast_treat (s : Situated) : contrast level treat s = s.2 := by
  simp [contrast, level, treat]

/-- **The effect is not homogeneous.**  Two states with the same visible level
and different susceptibilities respond differently, so "the effect of the
treatment" is not a well-defined quantity. -/
theorem contrast_not_homogeneous : ¬ Homogeneous level treat := by
  refine not_homogeneous_of_split (x₁ := (0, 0)) (x₂ := (0, 1)) ?_
  simp [level, treat]

/-- **Observation is not intervention**, on the same witness: the two states are
observationally identical before the action and different after it. -/
theorem observation_not_intervention :
    level (0, 0) = level (0, 1) ∧ level (treat (0, 0)) ≠ level (treat (0, 1)) := by
  refine ⟨rfl, ?_⟩
  simp [level, treat]

/-- Hence no function of the pre-intervention observation is the
post-intervention observation. -/
theorem level_not_determines_post : ¬ Determines level (fun s => level (treat s)) :=
  not_determines_of_collision observation_not_intervention.1 observation_not_intervention.2

/-- **The action can reverse the observed order.**  State `a` is observed below
state `b` before the action and above it after, so a monotone reading of the
observation does not survive the intervention. -/
theorem intervention_can_reverse_ordering :
    level ((0 : ℤ), (5 : ℤ)) < level ((1 : ℤ), (0 : ℤ)) ∧
      level (treat ((1 : ℤ), (0 : ℤ))) < level (treat ((0 : ℤ), (5 : ℤ))) := by
  constructor <;> simp [level, treat]

/-- The coordinate form of the label theorem: a consumer that reads the hidden
coordinate is not determined by the visible one. -/
theorem label_not_determines_effect :
    ¬ Determines (fun s : Situated => s.1) (fun s : Situated => s.2) :=
  not_determines_of_collision (x₁ := (0, 0)) (x₂ := (0, 1)) rfl (by decide)

/-! ## The corpus instance -/

/-- Mirror of the Agda `InterventionLabel`: one label. -/
inductive InterventionLabel
  /-- The single nominal intervention the module considers. -/
  | expandedSubsidisedECEC
  deriving DecidableEq, Repr, Fintype

/-- Mirror of the Agda `ObservedFamilyPosition`. -/
inductive ObservedFamilyPosition
  /-- The higher observed position. -/
  | observedHigherResource
  /-- The lower observed position. -/
  | observedLowerResource
  deriving DecidableEq, Repr, Fintype

/-- Mirror of the Agda `HiddenCounterfactual`: what the intervention replaces. -/
inductive HiddenCounterfactual
  /-- The intervention displaces a stronger alternative. -/
  | strongerAlternativeCare
  /-- The intervention displaces a weaker alternative. -/
  | weakerAlternativeCare
  deriving DecidableEq, Repr, Fintype

/-- Mirror of the Agda `EffectDirection`. -/
inductive EffectDirection
  /-- The effect points the wrong way. -/
  | adverseDirection
  /-- The effect points the right way. -/
  | beneficialDirection
  deriving DecidableEq, Repr, Fintype

/-- Mirror of the Agda `SituatedExposure`. -/
structure SituatedExposure where
  /-- The nominal intervention. -/
  intervention : InterventionLabel
  /-- The observed position. -/
  observedPosition : ObservedFamilyPosition
  /-- The counterfactual the intervention displaces. -/
  counterfactual : HiddenCounterfactual
  deriving DecidableEq, Repr

/-- The label projection. -/
def interventionProjection (e : SituatedExposure) : InterventionLabel := e.intervention

/-- The effect, defined by constructor patterns on the hidden coordinate. -/
def counterfactualRelativeEffect : SituatedExposure → EffectDirection
  | ⟨_, _, .strongerAlternativeCare⟩ => .adverseDirection
  | ⟨_, _, .weakerAlternativeCare⟩ => .beneficialDirection

/-- The module's two named exposures. -/
def higherCounterfactualExposure : SituatedExposure :=
  ⟨.expandedSubsidisedECEC, .observedHigherResource, .strongerAlternativeCare⟩

/-- The second named exposure. -/
def lowerCounterfactualExposure : SituatedExposure :=
  ⟨.expandedSubsidisedECEC, .observedLowerResource, .weakerAlternativeCare⟩

/-- The Agda `sameInterventionDifferentEffect`. -/
theorem same_intervention_different_effect :
    counterfactualRelativeEffect higherCounterfactualExposure ≠
      counterfactualRelativeEffect lowerCounterfactualExposure := by decide

/-- The Agda `interventionLabelCannotDetermineEffect`, obtained from the generic
owner rather than from a bespoke witness combinator. -/
theorem intervention_label_cannot_determine_effect :
    ¬ Determines interventionProjection counterfactualRelativeEffect :=
  not_determines_of_collision (x₁ := higherCounterfactualExposure)
    (x₂ := lowerCounterfactualExposure) rfl same_intervention_different_effect

/-- With one label the projection is constant, so the failure is unavoidable:
*every* non-constant consumer fails to factor through it. -/
theorem interventionProjection_constant (e f : SituatedExposure) :
    interventionProjection e = interventionProjection f := by
  obtain ⟨⟨⟩, _, _⟩ := e; obtain ⟨⟨⟩, _, _⟩ := f; rfl

/-- **The observed position does not determine the effect either.**  Fixing the
observed position and varying the counterfactual changes the effect. -/
theorem observed_position_cannot_determine_effect :
    ¬ Determines SituatedExposure.observedPosition counterfactualRelativeEffect :=
  not_determines_of_collision
    (x₁ := ⟨.expandedSubsidisedECEC, .observedHigherResource, .strongerAlternativeCare⟩)
    (x₂ := ⟨.expandedSubsidisedECEC, .observedHigherResource, .weakerAlternativeCare⟩)
    rfl (by decide)

/-- **The hidden coordinate is sufficient.**  This is the positive half of the
statement, and the corpus module does not record it: the effect is a function of
the counterfactual alone. -/
theorem counterfactual_determines_effect :
    Determines SituatedExposure.counterfactual counterfactualRelativeEffect := by
  rintro ⟨_, _, c₁⟩ ⟨_, _, c₂⟩ h
  cases c₁ <;> cases c₂ <;> simp_all [counterfactualRelativeEffect]

/-- So the situated state has exactly one essential coordinate for this
consumer: the counterfactual.  The label and the observed position are both
inessential, and the pair of them is *not* sufficient. -/
theorem effect_essential_set :
    Determines SituatedExposure.counterfactual counterfactualRelativeEffect ∧
      ¬ Determines
        (fun e : SituatedExposure => (e.intervention, e.observedPosition))
        counterfactualRelativeEffect :=
  ⟨counterfactual_determines_effect,
    not_determines_of_collision
      (x₁ := ⟨.expandedSubsidisedECEC, .observedHigherResource, .strongerAlternativeCare⟩)
      (x₂ := ⟨.expandedSubsidisedECEC, .observedHigherResource, .weakerAlternativeCare⟩)
      rfl (by decide)⟩

/-! ### The module's second witness: a subgroup label -/

/-- Mirror of the Agda `WithinGroupState`. -/
inductive WithinGroupState
  /-- The member of the group with the better counterfactual. -/
  | groupBetterCounterfactual
  /-- The member with the worse counterfactual. -/
  | groupWorseCounterfactual
  deriving DecidableEq, Repr, Fintype

/-- The observed group is the same for both members. -/
def observedGroupProjection (_ : WithinGroupState) : Unit := ()

/-- Their effects differ. -/
def withinGroupEffect : WithinGroupState → EffectDirection
  | .groupBetterCounterfactual => .adverseDirection
  | .groupWorseCounterfactual => .beneficialDirection

/-- The Agda `observedGroupCannotDetermineIndividualEffect`. -/
theorem observed_group_cannot_determine_individual_effect :
    ¬ Determines observedGroupProjection withinGroupEffect :=
  not_determines_of_collision (x₁ := .groupBetterCounterfactual)
    (x₂ := .groupWorseCounterfactual) rfl (by decide)

/-- And the general reason, which is worth separating from the witness: a
constant observation determines only constant consumers. -/
theorem constant_observation_determines_only_constants {X Y Z : Type}
    {O : X → Y} (hO : ∀ x y, O x = O y) {C : X → Z} (h : Determines O C) (x y : X) :
    C x = C y := h x y (hO x y)

end Integration.CounterfactualEffect
