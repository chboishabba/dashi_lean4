/-!
DASHI reconstruction of institutional feasible choice.
Source provenance: Forrest Landry, "An Immanent Metaphysics",
https://civilizationemerging.com/wp-content/uploads/2020/06/An-Immanent-Metaphysics-Forrest-Landry.pdf
(section "Self of Choice", p. 40); Forrest Landry interviewed by
Jim Rutt, "Immanent Metaphysics: Part 2 (EP109)",
https://jimrutt.substack.com/p/ep109-forrest-landry-on-immanent-079 .
Prompt context: screenshot of Rob McNamara / uvsmpub,
"A System of Wrong, Part 4: The Grid" (episode body not verified).

All definitions, counterexamples and theorems below are DASHI-authored
reconstructions, NOT propositions proved by the named sources.
No citation supplies a kernel theorem, empirical fact, or legal conclusion.
-/

namespace Dashi.InstitutionalAgency

universe u v w

structure ChoiceEnvironment (Agent : Type u) (State : Type v)
    (Action : Type w) where
  offered : Agent → State → Action → Prop
  viable : Agent → State → Action → Prop
  viability_sound : ∀ a s x, viable a s x → offered a s x

def Nominal {A : Type u} {S : Type v} {X : Type w}
    (e : ChoiceEnvironment A S X) (a : A) (s : S) : Set X :=
  {x | e.offered a s x}

def Feasible {A : Type u} {S : Type v} {X : Type w}
    (e : ChoiceEnvironment A S X) (a : A) (s : S) : Set X :=
  {x | e.viable a s x}

theorem feasible_subset_nominal {A : Type u} {S : Type v} {X : Type w}
    (e : ChoiceEnvironment A S X) (a : A) (s : S) :
    Feasible e a s ⊆ Nominal e a s :=
  fun _ hx => e.viability_sound a s _ hx

inductive ContractOption where
  | accept
  | reject
  deriving DecidableEq

def example : ChoiceEnvironment Unit Unit ContractOption where
  offered := fun _ _ _ => True
  viable := fun _ _ x => x = .accept
  viability_sound := by intro _ _ _ _; trivial

theorem offered_accept : example.offered () () .accept := trivial
theorem offered_reject : example.offered () () .reject := trivial
theorem feasible_accept : example.viable () () .accept := rfl
theorem reject_not_feasible : ¬ example.viable () () .reject := by
  decide

theorem viable_only_accept (x : ContractOption)
    (hx : example.viable () () x) : x = .accept := hx

structure InstitutionalDependency
    (Agent : Type u) (Institution : Type v) (Resource : Type w)
    (Goal : Type) where
  controls : Institution → Resource → Prop
  depends : Agent → Resource → Goal → Prop

def StructuralPower {A : Type u} {I : Type v} {R : Type w}
    {G : Type} (d : InstitutionalDependency A I R G)
    (i : I) (a : A) (g : G) : Prop :=
  ∃ r : R, d.controls i r ∧ d.depends a r g

end Dashi.InstitutionalAgency
