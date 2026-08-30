import Integration.Experiment.Dimension
import Integration.FactorisationCollision

/-!
# Lane 1b — the typed quantity graph

A law in this calculus is an *edge*: a typed arity, an evaluation rule, and —
mandatorily — a provenance, a list of assumptions, a validity predicate on the
input values and a first-order sensitivity vector used later by the uncertainty
lane.  A law with no assumptions and a law with stoichiometric assumptions are
**different objects**, and the file proves the difference is not decorative.

## The distinction the lane is asked for

```
Q = I t          dimensional identity, no free parameter
n = Q / (z F)    constitutive model, parameterised by z and by an efficiency
```

`charge_factors_through_current_and_time` shows the first is a function of its
declared inputs.  `amount_does_not_factor_through_charge` shows the second is
**not** a function of charge alone: it is a `Collision` of the existing
factorisation owner, so "this edge carries assumptions" is a determination
failure and not a label.  `efficiency_collides_even_with_z_known` shows that
naming the stoichiometric number is not enough either.

## Contents

* `§1` `LawKind`, `Law`, typed application, and the well-typedness criterion;
* `§2` the electrochemical edges `Q = It`, `E = VQ`, `n = Q/(zF)`, `m = nM`;
* `§3` composition of edges: a path is well typed iff adjacent dimensions
  agree, and a nonsense composition is rejected;
* `§4` the dimensional-law/model-law separation, via collisions;
* `§5` validity domains: an edge applied outside its declared domain returns
  nothing, and the domain is not recoverable from the values it returns.
-/

namespace Integration.Experiment.QuantityGraph

open Integration.Experiment.Dimension
open Integration.CoordinateSufficiency
open Integration.FactorisationCollision

/-! ## §1 Laws as typed edges -/

/-- The epistemic kind of an edge.  This is data attached to the edge, and §4
proves the kinds behave differently rather than merely being named
differently. -/
inductive LawKind
  /-- A definitional or dimensional identity with no free parameter. -/
  | dimensionalIdentity
  /-- A constitutive model: correct only under stated assumptions, and
  parameterised by quantities that are not among its declared inputs. -/
  | constitutiveModel
  /-- An empirical correlation fitted on a declared range. -/
  | empiricalCorrelation
  deriving DecidableEq, Repr

/-- An edge of the quantity graph. -/
structure Law where
  /-- A label for the edge. -/
  name : String
  /-- The dimensions of the inputs, in order. -/
  inputs : List Dim
  /-- The dimension of the output. -/
  output : Dim
  /-- Where the equation comes from. -/
  provenance : String
  /-- The assumptions under which the edge is licensed; `[]` only for a
  dimensional identity. -/
  assumptions : List String
  /-- The declared domain of validity, as a predicate on the input values. -/
  validity : List ℚ → Bool
  /-- The evaluation rule on the input values. -/
  eval : List ℚ → ℚ
  /-- The first-order sensitivities `∂out/∂inᵢ` at the given inputs, used by the
  uncertainty lane. -/
  sensitivity : List ℚ → List ℚ
  /-- The epistemic kind of the edge. -/
  kind : LawKind

/-- The declared input dimensions of a list of quantities. -/
def dims (xs : List Quantity) : List Dim := xs.map Quantity.dim

/-- **Typed application.**  An edge applies to an argument list only when the
dimensions match its declared arity *and* the values lie in its validity
domain. -/
def Law.apply (L : Law) (xs : List Quantity) : Option Quantity :=
  if dims xs = L.inputs ∧ L.validity (xs.map Quantity.value) = true then
    some ⟨L.output, L.eval (xs.map Quantity.value)⟩
  else none

/-- **The well-typedness criterion**, exactly. -/
theorem Law.apply_isSome_iff (L : Law) (xs : List Quantity) :
    (L.apply xs).isSome = true ↔
      (dims xs = L.inputs ∧ L.validity (xs.map Quantity.value) = true) := by
  unfold Law.apply; split <;> simp_all

/-- An applied edge always returns a quantity of its declared output
dimension. -/
theorem Law.apply_dim {L : Law} {xs : List Quantity} {q : Quantity}
    (h : L.apply xs = some q) : q.dim = L.output := by
  unfold Law.apply at h; split at h
  · cases h; rfl
  · exact absurd h (by simp)

/-! ## §2 The electrochemical edges -/

/-- The Faraday constant, in coulomb per mole (rounded to the rational value
used throughout this development). -/
def faraday : ℚ := 96485

/-- `Q = I t`: charge from current and time.  No assumptions, no parameters. -/
def chargeLaw : Law where
  name := "Q = I t"
  inputs := [Dim.ampere, Dim.second]
  output := Dim.coulomb
  provenance := "definition of electric charge as the time integral of current"
  assumptions := []
  validity := fun _ => true
  eval := fun vs => match vs with | [i, t] => i * t | _ => 0
  sensitivity := fun vs => match vs with | [i, t] => [t, i] | _ => []
  kind := .dimensionalIdentity

/-- `E = V Q`: energy from potential and charge, at constant potential. -/
def energyLaw : Law where
  name := "E = V Q"
  inputs := [Dim.volt, Dim.coulomb]
  output := Dim.joule
  provenance := "work done moving charge Q through a constant potential V"
  assumptions := ["potential held constant over the charge transferred"]
  validity := fun _ => true
  eval := fun vs => match vs with | [v, q] => v * q | _ => 0
  sensitivity := fun vs => match vs with | [v, q] => [q, v] | _ => []
  kind := .constitutiveModel

/-- `n = Q / (z F)`: Faraday's law of electrolysis, for stoichiometric number
`z` and coulombic efficiency `eta`.  Both are parameters of the *edge*, not
inputs to it — which is exactly what §4 makes formal. -/
def amountLaw (z eta : ℚ) : Law where
  name := "n = eta Q / (z F)"
  inputs := [Dim.coulomb]
  output := Dim.mole
  provenance := "Faraday's law of electrolysis"
  assumptions :=
    ["a single faradaic reaction with stoichiometric number z",
     "coulombic efficiency eta (no parasitic side reactions beyond it)",
     "no self-discharge over the interval"]
  validity := fun vs => match vs with | [q] => decide (0 ≤ q) | _ => false
  eval := fun vs => match vs with | [q] => eta * q / (z * faraday) | _ => 0
  sensitivity := fun vs => match vs with | [_] => [eta / (z * faraday)] | _ => []
  kind := .constitutiveModel

/-- `m = n M`: mass from amount of substance and molar mass. -/
def massLaw : Law where
  name := "m = n M"
  inputs := [Dim.mole, Dim.kgPerMole]
  output := Dim.kilogram
  provenance := "definition of molar mass"
  assumptions := []
  validity := fun _ => true
  eval := fun vs => match vs with | [n, m] => n * m | _ => 0
  sensitivity := fun vs => match vs with | [n, m] => [m, n] | _ => []
  kind := .dimensionalIdentity

/-- A worked application: 2 A for 5 s is 10 C. -/
theorem chargeLaw_applies :
    chargeLaw.apply [⟨Dim.ampere, 2⟩, ⟨Dim.second, 5⟩] = some ⟨Dim.coulomb, 10⟩ := by
  norm_num [Law.apply, chargeLaw, dims]

/-- And the same edge rejects a voltage where it wants a current. -/
theorem chargeLaw_rejects_voltage :
    chargeLaw.apply [⟨Dim.volt, 2⟩, ⟨Dim.second, 5⟩] = none := by
  simp [Law.apply, chargeLaw, dims]
  decide

/-- Faraday's edge rejects a negative charge, which is outside its declared
validity domain even though the dimensions are right. -/
theorem amountLaw_rejects_outside_validity (z eta : ℚ) :
    (amountLaw z eta).apply [⟨Dim.coulomb, -1⟩] = none := by
  simp [Law.apply, amountLaw, dims]

/-! ## §3 Composing edges -/

/-- Two edges compose at position `i` when the first edge's output dimension is
the dimension the second expects there.  The check is a computation. -/
def composable (L₁ L₂ : Law) (i : ℕ) : Bool := L₂.inputs[i]? == some L₁.output

/-- `Q = It` feeds Faraday's law: charge out, charge in. -/
theorem charge_feeds_amount (z eta : ℚ) : composable chargeLaw (amountLaw z eta) 0 = true := rfl

/-- Faraday's law feeds the molar-mass edge. -/
theorem amount_feeds_mass (z eta : ℚ) : composable (amountLaw z eta) massLaw 0 = true := rfl

/-- **A nonsense composition is rejected**: charge is not a potential, so the
charge edge does not feed the energy edge's first slot. -/
theorem charge_does_not_feed_energy_potential_slot :
    composable chargeLaw energyLaw 0 = false := rfl

/-- The end-to-end path `I, t ↦ Q ↦ n ↦ m`, evaluated by typed application at
each step, with every intermediate dimension checked. -/
def deposit (I t z eta M : ℚ) : Option Quantity := do
  let q ← chargeLaw.apply [⟨Dim.ampere, I⟩, ⟨Dim.second, t⟩]
  let n ← (amountLaw z eta).apply [q]
  massLaw.apply [n, ⟨Dim.kgPerMole, M⟩]

/-- A worked end-to-end evaluation: 1 A for 3600 s at `z = 1`, unit efficiency
and the molar mass of lithium (6.941 g/mol) deposits `3600 · 0.006941/96485`
kilograms of lithium, and the result is typed as a mass. -/
theorem deposit_lithium :
    deposit 1 3600 1 1 (6941/1000000) =
      some ⟨Dim.kilogram, 3600 * (6941/1000000) / 96485⟩ := by
  norm_num [deposit, Law.apply, chargeLaw, amountLaw, massLaw, dims, faraday]

/-! ## §4 A dimensional identity is not a constitutive model -/

/-- The state of the electrochemical cell as far as this lane is concerned: the
applied current and duration, the stoichiometric number and the coulombic
efficiency.  The last two are *not* measured by a coulomb counter. -/
structure CellRun where
  /-- Applied current. -/
  current : ℚ
  /-- Duration. -/
  duration : ℚ
  /-- Stoichiometric number of the faradaic reaction. -/
  z : ℚ
  /-- Coulombic efficiency. -/
  eta : ℚ
  deriving DecidableEq

/-- Charge transferred during a run. -/
def CellRun.charge (r : CellRun) : ℚ := r.current * r.duration

/-- Amount of substance converted during a run, by Faraday's law. -/
def CellRun.amount (r : CellRun) : ℚ := r.eta * r.charge / (r.z * faraday)

/-- **The dimensional identity is a function of its declared inputs.**  Charge
is determined by current and time and by nothing else: this edge has no hidden
parameter. -/
theorem charge_factors_through_current_and_time :
    Determines (fun r : CellRun => (r.current, r.duration)) CellRun.charge := by
  intro x y h
  have h1 : x.current = y.current := congrArg Prod.fst h
  have h2 : x.duration = y.duration := congrArg Prod.snd h
  simp [CellRun.charge, h1, h2]

/-- **The constitutive model is not.**  Two runs pass exactly the same charge
and convert different amounts of substance, because they run different
reactions.  This is a `Collision` of the existing factorisation owner, so every
consequence of that owner applies: no reading of the charge returns the amount,
and no post-processing repairs it. -/
def amountCollision : Collision CellRun.charge CellRun.amount where
  left := ⟨1, 96485, 1, 1⟩
  right := ⟨1, 96485, 2, 1⟩
  distinct := by decide
  collide := by norm_num [CellRun.charge]
  separate := by norm_num [CellRun.amount, CellRun.charge, faraday]

/-- Hence charge does not determine amount. -/
theorem amount_does_not_factor_through_charge :
    ¬ Determines CellRun.charge CellRun.amount :=
  amountCollision.not_determines

/-- And **no** coulomb-counting algorithm whatsoever returns the amount: the
obstruction is the representation, not the estimator. -/
theorem no_coulomb_counter_returns_the_amount (f : ℚ → ℚ) :
    ¬ ∀ r : CellRun, r.amount = f r.charge :=
  amountCollision.no_reading f

/-- **Naming the stoichiometric number is not enough.**  Even knowing `(Q, z)`,
the unquantified coulombic efficiency leaves the amount undetermined: a second
assumption of the same edge, and a second collision. -/
def efficiencyCollision :
    Collision (fun r : CellRun => (r.charge, r.z)) CellRun.amount where
  left := ⟨1, 96485, 1, 1⟩
  right := ⟨1, 96485, 1, 1/2⟩
  distinct := by
    intro h
    have := congrArg CellRun.eta h
    norm_num at this
  collide := by norm_num [CellRun.charge]
  separate := by norm_num [CellRun.amount, CellRun.charge, faraday]

theorem efficiency_collides_even_with_z_known :
    ¬ Determines (fun r : CellRun => (r.charge, r.z)) CellRun.amount :=
  efficiencyCollision.not_determines

/-- **What does close it.**  Charge together with *both* declared parameters
determines the amount: the assumption list of the edge is exactly the extra
information the collision demands, and the graph names it. -/
theorem amount_determined_by_charge_and_both_parameters :
    Determines (fun r : CellRun => (r.charge, r.z, r.eta)) CellRun.amount := by
  intro x y h
  have h1 : x.charge = y.charge := congrArg Prod.fst h
  have h2 : x.z = y.z := congrArg (fun p => p.2.1) h
  have h3 : x.eta = y.eta := congrArg (fun p => p.2.2) h
  simp [CellRun.amount, h1, h2, h3]

/-- The separation stated as the lane asks for it: the two edges are both
dimensionally impeccable, and exactly one of them is a function of its declared
inputs. -/
theorem dimensional_law_versus_model_law :
    Determines (fun r : CellRun => (r.current, r.duration)) CellRun.charge ∧
      ¬ Determines CellRun.charge CellRun.amount ∧
      chargeLaw.assumptions = [] ∧ (amountLaw 1 1).assumptions ≠ [] :=
  ⟨charge_factors_through_current_and_time, amount_does_not_factor_through_charge,
    rfl, by simp [amountLaw]⟩

/-! ## §5 Validity domains -/

/-- An edge applied outside its declared validity domain returns nothing, even
when every dimension is correct — so the domain is a typing condition of the
same standing as the dimensions. -/
theorem outside_validity_is_a_type_error (z eta : ℚ) (q : ℚ) (h : q < 0) :
    (amountLaw z eta).apply [⟨Dim.coulomb, q⟩] = none := by
  have : ¬ (0 ≤ q) := by linarith
  simp [Law.apply, amountLaw, dims, this]

/-- **The validity domain is not recoverable from the returned values.**  Two
edges agree on every value they both return and declare different domains, so a
consumer that sees only outputs cannot reconstruct where the model was
licensed. -/
theorem validity_domain_is_not_observable :
    ∃ L₁ L₂ : Law,
      L₁.validity ≠ L₂.validity ∧ L₁.eval = L₂.eval ∧
      L₁.apply [⟨Dim.coulomb, 1⟩] = L₂.apply [⟨Dim.coulomb, 1⟩] := by
  refine ⟨amountLaw 1 1, { amountLaw 1 1 with validity := fun _ => true }, ?_, rfl, ?_⟩
  · intro h
    have h1 := congrFun h [(-1 : ℚ)]
    norm_num [amountLaw] at h1
  · simp [Law.apply, amountLaw, dims]

end Integration.Experiment.QuantityGraph
