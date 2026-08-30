import Integration.DescentLevel
import Integration.StructureMorphism

/-!
# Path-order information, and the resolution at which it becomes visible

Two transports of the same state need not commute.  A coarse observation of the
two endpoints may nevertheless agree.  That configuration —

```
   A (B x) ≠ B (A x)          (fine noncommutativity)
   π (A (B x)) = π (B (A x))  (coarse flatness)
```

— is the precise sense in which an observation can erase path order.  This file
owns it, domain-neutrally, and then answers the sharper question the corpus's
`Integration.DescentLevel` machinery makes available: *at which observational
resolution does the path-order information first disappear?*

Contents.

* `CommPair`, `FineNoncommutative`, `CoarseFlat` — the three notions;
* `coarseFlat_of_exact_pair` — the positive control: if the observer intertwines
  both transports with downstream transports that commute, the coarse layer is
  flat automatically.  So coarse flatness is not by itself evidence of anything;
  the content is in its *combination* with fine noncommutativity;
* `hidden_order_information` — the general statement: under both hypotheses the
  coarse defect vanishes identically while the fine defect does not, so no
  function of the observed endpoint can be the fine defect;
* `Cubie`, `tA`, `tB`, `obs` — an explicit four-state carrier with two transports realising it, and
  `cubie_hidden_order` verifying both hypotheses by decision;
* `commDefectVal` — the fine defect as a number, `commutator_defect_pos`;
* `cubie_coarsest_sufficient` — the **answer to the resolution question** on
  this carrier: the commutator defect factors through the two-valued observer
  and not through the trivial one, so its coarsest sufficient observation is
  level one of the tower.  This is a computed instance of "the minimum
  observational resolution at which path-order information survives", not a
  claim about any physical measurement.

Nothing here constructs a connection, a curvature tensor, or a metric, and no
claim is made that any physical system realises this carrier.  What is proved is
the finite structural pattern: *fine noncommutativity with coarse flatness*, and
its descent level.
-/

namespace Integration.CommutatorObservability

open Integration.DescentLevel
open Integration.DescentLevel.LayerTower
open Integration.StructureMorphism

variable {X Y : Type*}

/-! ## The three notions -/

/-- The unordered pair of endpoints of the two orders of transport. -/
def CommPair (A B : X → X) (x : X) : X × X := (A (B x), B (A x))

/-- The transports fail to commute at some state. -/
def FineNoncommutative (A B : X → X) : Prop := ∃ x, A (B x) ≠ B (A x)

/-- The observer cannot distinguish the two orders, at any state. -/
def CoarseFlat (π : X → Y) (A B : X → X) : Prop := ∀ x, π (A (B x)) = π (B (A x))

/-- **Positive control.**  If the observer exactly intertwines each transport
with a downstream transport, and the downstream transports commute, then the
coarse layer is flat.  Coarse flatness on its own is therefore cheap. -/
theorem coarseFlat_of_exact_pair {π : X → Y} {A B : X → X} {A' B' : Y → Y}
    (hA : Exact π A A') (hB : Exact π B B') (hcomm : ∀ y, A' (B' y) = B' (A' y)) :
    CoarseFlat π A B := by
  intro x
  rw [hA (B x), hB x, hB (A x), hA x, hcomm (π x)]

/-- **The pattern.**  Fine noncommutativity together with coarse flatness says
exactly that the observed endpoint carries none of the path-order information:
the coarse "defect" is identically trivial, while the fine one is not. -/
theorem hidden_order_information {π : X → Y} {A B : X → X}
    (hflat : CoarseFlat π A B) (hfine : FineNoncommutative A B) :
    (∀ x, π (CommPair A B x).1 = π (CommPair A B x).2) ∧
      ∃ x, (CommPair A B x).1 ≠ (CommPair A B x).2 :=
  ⟨hflat, hfine⟩

/-- And consequently the fine endpoint is not a function of the observed
endpoint: any putative reconstruction of `A (B x)` from `π (A (B x))` would have
to return `B (A x)` as well. -/
theorem no_reconstruction_of_order {π : X → Y} {A B : X → X}
    (hflat : CoarseFlat π A B) (hfine : FineNoncommutative A B) :
    ¬ ∃ r : Y → X, ∀ x, r (π x) = x := by
  rintro ⟨r, hr⟩
  obtain ⟨x, hx⟩ := hfine
  exact hx (by rw [← hr (A (B x)), hflat x, hr])

/-! ## An explicit carrier -/

/-- The four-state carrier. -/
abbrev Cubie : Type := Bool × Bool

/-- The first transport: exchange the two coordinates. -/
def tA (p : Cubie) : Cubie := (p.2, p.1)

/-- The second transport: overwrite the second coordinate with the first. -/
def tB (p : Cubie) : Cubie := (p.1, p.1)

/-- The observer: "are the two coordinates equal?". -/
def obs (p : Cubie) : Bool := decide (p.1 = p.2)

/-- **Both hypotheses hold on this carrier**, by decision. -/
theorem cubie_hidden_order : CoarseFlat obs tA tB ∧ FineNoncommutative tA tB := by
  constructor
  · rintro ⟨a, b⟩
    revert a b
    decide
  · exact ⟨(false, true), by decide⟩

/-- A numeric readout of the fine state. -/
def fineVal (p : Cubie) : ℝ := (if p.1 then 2 else 0) + (if p.2 then 1 else 0)

/-- The fine commutator defect, as a number. -/
noncomputable def commDefectVal (x : Cubie) : ℝ :=
  |fineVal (tA (tB x)) - fineVal (tB (tA x))|

/-- In closed form: the defect is `3` on the unequal states and `0` on the equal
ones, so it *is* a function of the two-valued observation. -/
theorem commDefectVal_eq (x : Cubie) : commDefectVal x = if obs x then 0 else 3 := by
  rcases x with ⟨a, b⟩
  cases a <;> cases b <;> norm_num [commDefectVal, fineVal, tA, tB, obs]

/-- The defect is strictly positive somewhere: the two orders of transport are
genuinely distinguishable at the fine level. -/
theorem commutator_defect_pos : 0 < commDefectVal (false, true) := by
  norm_num [commDefectVal, fineVal, tA, tB]

/-- The coarse observation of the two endpoints, in contrast, always agrees. -/
theorem coarse_defect_zero (x : Cubie) : obs (tA (tB x)) = obs (tB (tA x)) :=
  cubie_hidden_order.1 x

/-! ## The resolution question -/

/-- The tower `Cubie → Bool → Unit`. -/
def cubieTower : LayerTower := twoStepTower obs (fun _ : Bool => ())

/-- The defect *is* a function of the two-valued observation. -/
theorem commDefect_factorsAt_one : cubieTower.FactorsAt commDefectVal 1 := by
  refine ⟨fun (b : Bool) => if b then 0 else 3, ?_⟩
  exact commDefectVal_eq

/-- It is not a function of the trivial observation, because it is not
constant. -/
theorem commDefect_not_factorsAt_two : ¬ cubieTower.FactorsAt commDefectVal 2 := by
  rw [LayerTower.factorsAt_iff_fibre]
  intro h
  have := h (false, true) (false, false) rfl
  rw [show commDefectVal (false, false) = 0 by norm_num [commDefectVal, fineVal, tA, tB]] at this
  exact absurd this (ne_of_gt commutator_defect_pos)

/-- **The coarsest sufficient observation for the path-order defect on this
carrier is level one.**  Below that resolution the commutator becomes invisible;
at that resolution it is exactly reconstructible. -/
theorem cubie_coarsest_sufficient : cubieTower.CoarsestSufficient commDefectVal 1 :=
  ⟨commDefect_factorsAt_one, commDefect_not_factorsAt_two⟩

end Integration.CommutatorObservability
