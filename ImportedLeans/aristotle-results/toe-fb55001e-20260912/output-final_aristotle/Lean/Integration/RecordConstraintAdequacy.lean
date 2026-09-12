import Integration.FactorisationCollision

/-!
# Contract adequacy: what inhabiting a record does and does not prove

The corpus repeatedly discovered the same defect in different lanes: a record
field whose *name* describes a mathematical property, whose *type* imposes no
constraint.  `Synthesis.PhysicsInterfaces` found it in the gauge, spin and
unitary interfaces; `Cuisine.LedgerPattern` found it in the `Bool`-plus-`= false`
ledgers; `Cuisine.Publication` and `Cuisine.CarryingCapacity` found it in status
fields unconstrained by the components they are named after.

Those were separate discoveries about separate records.  This file owns the
pattern once, as a statement about an arbitrary contract, and proves the four
facts the audit workflow needs.

## The audit

A **contract** is a predicate `Contract : M → Prop` on models; the property it
is *named* for is another predicate `Intended : M → Prop`.

* `Adequate Contract Intended` — every model of the contract has the property.
* `Countermodel` — a model of the contract without the property; `not_adequate`
  turns one into a refutation, which is exactly the adversarial-inhabitance test:
  *can I satisfy this record with an object that obviously lacks the property?*
* `adequate_iff_no_countermodel` — the two are exhaustive: adequacy is precisely
  the absence of a countermodel, so the search for a countermodel is a decision
  procedure for adequacy, not a heuristic.
* `empty_contract_is_adequate` — soundness alone is worthless: the unsatisfiable
  contract is adequate for *every* intended property.  Hence `Audited`, which
  demands soundness **and** a model that has the property.
* `Audited.not_vacuous` — an audited contract is satisfiable, and
  `audited_no_countermodel` — it has no countermodel.

## Free fields

`FlagFree spec` says a flag field is unconstrained by the record's data.  Then:

* `free_flag_not_determined` — the flag is not determined by the data;
* `freeFlagCollision` — and, as an `Integration.FactorisationCollision.Collision`,
  the failure is inherited by every downstream reading of the data, so no later
  computation recovers the claimed dependency;
* `trivialObligationEquivData` — a record all of whose obligations are `True` is
  equivalent to its bare data, so inhabiting it proves exactly what exhibiting
  the data proves;
* `Ledger` generalises the cuisine `Bool`-plus-equation pattern to any decidable
  equality and any pinned value: `ledger_no_information` says a predicate holds
  of some ledger iff it holds of the canonical one.

Nothing here is about any domain; the carriers are arbitrary types.
-/

namespace Integration.RecordConstraintAdequacy

open Integration.FactorisationCollision

variable {M : Type*}

/-! ## Contracts, adequacy and countermodels -/

/-- The contract `Contract` **is adequate for** the property `Intended` when
every model satisfying the contract has the property.  This is the only sense in
which "inhabiting the record proves the property" can be true. -/
def Adequate (Contract Intended : M → Prop) : Prop := ∀ m, Contract m → Intended m

/-- A **countermodel**: an object satisfying the contract that lacks the property
the contract is named for. -/
structure Countermodel (Contract Intended : M → Prop) where
  /-- The offending object. -/
  model : M
  /-- It satisfies every field of the contract. -/
  satisfies : Contract model
  /-- It lacks the intended property. -/
  violates : ¬ Intended model

/-- A countermodel refutes adequacy. -/
theorem Countermodel.not_adequate {Contract Intended : M → Prop}
    (w : Countermodel Contract Intended) : ¬ Adequate Contract Intended :=
  fun h => w.violates (h w.model w.satisfies)

/-- **The adversarial test is complete.**  A contract is adequate exactly when no
countermodel exists, so failing to find one is the only thing left to prove. -/
theorem adequate_iff_no_countermodel (Contract Intended : M → Prop) :
    Adequate Contract Intended ↔ IsEmpty (Countermodel Contract Intended) := by
  constructor
  · intro h
    exact ⟨fun w => w.not_adequate h⟩
  · intro h m hm
    by_contra hi
    exact h.elim ⟨m, hm, hi⟩

/-- **Soundness alone is worthless.**  The unsatisfiable contract is adequate for
every property whatsoever. -/
theorem empty_contract_is_adequate (Intended : M → Prop) :
    Adequate (fun _ => False) Intended := fun _ h => h.elim

/-- **The other degenerate case.**  The contract that says nothing is adequate
only for properties that hold of every model. -/
theorem trivial_contract_adequate_iff (Intended : M → Prop) :
    Adequate (fun _ => True) Intended ↔ ∀ m, Intended m :=
  ⟨fun h m => h m trivial, fun h m _ => h m⟩

/-- A contract that has passed the audit: it is sound for the property, and it is
witnessed by a model that really has the property. -/
structure Audited (Contract Intended : M → Prop) where
  /-- Every model of the contract has the property. -/
  sound : Adequate Contract Intended
  /-- Some model satisfies the contract and has the property. -/
  witness : M
  /-- The witness satisfies the contract … -/
  witness_satisfies : Contract witness
  /-- … and has the property. -/
  witness_intended : Intended witness

/-- An audited contract is satisfiable — it is not adequate merely by being
empty. -/
theorem Audited.not_vacuous {Contract Intended : M → Prop}
    (a : Audited Contract Intended) : ∃ m, Contract m := ⟨a.witness, a.witness_satisfies⟩

/-- An audited contract has no countermodel. -/
theorem audited_no_countermodel {Contract Intended : M → Prop}
    (a : Audited Contract Intended) : IsEmpty (Countermodel Contract Intended) :=
  (adequate_iff_no_countermodel Contract Intended).1 a.sound

/-- The unsatisfiable contract is *not* audited for a property that some model
lacks: adequacy and non-vacuity are independent requirements. -/
theorem empty_contract_not_audited (Intended : M → Prop) :
    IsEmpty (Audited (fun _ : M => False) Intended) :=
  ⟨fun a => a.witness_satisfies⟩

/-! ## Free fields -/

variable {D F : Type}

/-- The flag is **determined** by the data: the record's own fields pin it down. -/
def FlagDetermined (spec : D → F → Prop) : Prop := ∀ d f g, spec d f → spec d g → f = g

/-- The flag is **free**: every value of the flag is compatible with every value
of the data.  This is the shape of every field the audits found. -/
def FlagFree (spec : D → F → Prop) : Prop := ∀ d f, spec d f

/-- **A free flag is not determined.**  As soon as the flag carrier has two
values and the data carrier is inhabited, freedom refutes determination. -/
theorem free_flag_not_determined {spec : D → F → Prop} (h : FlagFree spec)
    (d : D) {f g : F} (hne : f ≠ g) : ¬ FlagDetermined spec :=
  fun hdet => hne (hdet d f g (h d f) (h d g))

/-- The failure as a collision of the "read the data" observation against the
"read the flag" consumer, on the record type `D × F`. -/
def freeFlagCollision (d : D) {f g : F} (hne : f ≠ g) :
    Collision (fun p : D × F => p.1) (fun p : D × F => p.2) where
  left := (d, f)
  right := (d, g)
  distinct := by
    intro h
    exact hne (congrArg Prod.snd h)
  collide := rfl
  separate := hne

/-- **No reading of the data returns a free flag.**  For every candidate rule
`r` computing the flag from the data there is a record on which it is wrong. -/
theorem free_flag_not_a_function_of_data (d : D) {f g : F} (hne : f ≠ g) (r : D → F) :
    ¬ ∀ p : D × F, p.2 = r p.1 := by
  intro h
  exact (freeFlagCollision d hne).no_reading r (fun p => h p)

/-- A record whose propositional obligations are all `True` is equivalent to its
bare data: inhabiting it proves exactly what exhibiting the data proves. -/
def trivialObligationEquivData (Data : Type*) : Subtype (fun _ : Data => True) ≃ Data :=
  Equiv.subtypeUnivEquiv (fun _ => trivial)

/-! ## The pinned-value ledger -/

variable {A : Type}

/-- The generic form of the corpus's `flag : Bool` / `flag = false` pattern: a
value together with a proof that it is a fixed constant. -/
def Ledger (a : A) : Type _ := { x : A // x = a }

/-- The ledger is uniquely inhabited. -/
instance (a : A) : Unique (Ledger a) where
  default := ⟨a, rfl⟩
  uniq := by rintro ⟨x, rfl⟩; rfl

/-- Hence it is equivalent to `Unit`. -/
def ledgerEquivUnit (a : A) : Ledger a ≃ Unit := Equiv.equivPUnit _

/-- **A ledger carries no information.**  Any property that some ledger entry has
is a property of the canonical entry, so a ledger separates nothing: it records
that a flag was never flipped, which is a fact about the development, not a proof
of the statement the field is named after. -/
theorem ledger_no_information (a : A) (P : Ledger a → Prop) :
    (∃ l, P l) ↔ P default := by
  constructor
  · rintro ⟨l, hl⟩
    rwa [Subsingleton.elim (default : Ledger a) l]
  · exact fun h => ⟨_, h⟩

/-- A ledger field is a free field in the sense above: pairing data with a ledger
constrains nothing, because the ledger component is constant. -/
theorem ledger_flag_free (a : A) : FlagFree (fun (_ : D) (_ : Ledger a) => True) :=
  fun _ _ => trivial

end Integration.RecordConstraintAdequacy
