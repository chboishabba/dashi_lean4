import Integration.CoordinateSufficiency

/-!
# Declared carriers: completeness, verification and sufficiency are all relative

Several corpus artefacts are *atlases*: an enumeration of sources, options or
cases, together with an explicit prose disclaimer that the enumeration is not
exhaustive.  (`DASHI/Culture/Cuisine/CuisineKnowledgeSourceAtlas.agda` and
`DASHI/Governance/RevolutionarySourceAtlas.agda` both carry a `String` field
saying the atlas "does not claim … exhaustive coverage".)  The disclaimer is the
right discipline; this file gives it a theorem, so the discipline is enforced
rather than asserted.

The single mathematical point is that **three different properties are all
relative to a declared carrier**, and none of them transfers to a larger one:

* an enumeration is exhaustive *of the states it declares*;
* a property is verified *on the states enumerated*;
* an observer is sufficient *for the states considered*.

## Contents

* `ExhaustiveOn`, `VerifiedOn` — the two enumeration notions;
* `universal_of_exhaustive` — **the transfer theorem**: checking a property on an
  enumeration is a universal claim exactly when the enumeration is exhaustive of
  the intended carrier.  This is the only route, and it makes the carrier
  explicit;
* `exterior_witness_refutes_exhaustion` — one element outside the enumeration
  refutes the exhaustion claim;
* `verified_not_universal` — and without exhaustion the transfer fails: an
  explicit property true on every enumerated element and false elsewhere;
* `exhaustion_flag_is_free` — a `Bool` field asserting coverage is free, so an
  inhabitant asserting it is a declaration and not evidence;
* `DeterminesOn`, `determinesOn_not_determines` — the observer form: an
  observation sufficient for a consumer on the declared carrier can fail to be
  sufficient on a larger one.  A model complete in its own chart says nothing
  about the exterior.

Nothing here is a claim about any atlas, source or authority.  The carriers are
`ℕ` and finite lists of numerals.
-/

namespace Integration.DeclaredCarrier

open Integration.CoordinateSufficiency

variable {X : Type}

/-! ## Enumerations -/

/-- The enumeration `l` is exhaustive of the declared carrier `S`. -/
def ExhaustiveOn (l : List X) (S : X → Prop) : Prop := ∀ x, S x → x ∈ l

/-- The property `P` has been checked on every enumerated element. -/
def VerifiedOn (P : X → Prop) (l : List X) : Prop := ∀ x ∈ l, P x

/-- **The transfer theorem.**  Checking a property on an enumeration establishes
it on a carrier exactly when the enumeration is exhaustive *of that carrier*.
Every enumeration-based universal claim passes through this statement, and it
cannot be applied without naming the carrier. -/
theorem universal_of_exhaustive {l : List X} {S P : X → Prop}
    (hex : ExhaustiveOn l S) (hver : VerifiedOn P l) : ∀ x, S x → P x :=
  fun x hx => hver x (hex x hx)

/-- One element outside the enumeration refutes exhaustion of any carrier
containing it. -/
theorem exterior_witness_refutes_exhaustion {l : List X} {S : X → Prop} {y : X}
    (hy : y ∉ l) (hS : S y) : ¬ ExhaustiveOn l S :=
  fun hex => hy (hex y hS)

/-- The enumeration used as a witness below. -/
def sample : List ℕ := [0, 1]

/-- The declared carrier it exhausts. -/
def declared (n : ℕ) : Prop := n < 2

/-- It really is exhaustive of the declared carrier. -/
theorem sample_exhaustive_on_declared : ExhaustiveOn sample declared := by
  intro n hn
  simp only [declared] at hn
  interval_cases n <;> simp [sample]

/-- **But not of the ambient type.**  So "the atlas is complete" is not a
property of the atlas: it is a property of the atlas together with a declared
carrier, and the two claims have different truth values here. -/
theorem sample_not_exhaustive_ambient : ¬ ExhaustiveOn sample (fun _ : ℕ => True) :=
  exterior_witness_refutes_exhaustion (y := 2) (by simp [sample]) trivial

/-- **Verification does not transfer past the declared carrier.**  Being smaller
than two is verified on every enumerated element and false at an element outside
the enumeration; the transfer theorem does not apply because its exhaustion
hypothesis fails for the ambient type. -/
theorem verified_not_universal :
    VerifiedOn (fun n : ℕ => n < 2) sample ∧ ¬ (fun n : ℕ => n < 2) 2 := by
  refine ⟨?_, by norm_num⟩
  intro n hn
  fin_cases hn <;> norm_num

/-- A record that merely *declares* coverage. -/
structure CoverageClaim where
  /-- Whether the artefact declares its enumeration exhaustive. -/
  claimsExhaustiveCoverage : Bool
  /-- Whether the artefact declares its sources to agree. -/
  claimsSourceAgreement : Bool
  deriving DecidableEq, Repr

/-- **A coverage flag is free.**  Two inhabitants agree on the second field and
disagree on the first, so setting the flag is a declaration and supplies no
`ExhaustiveOn` proof.  This is why the atlases' prose disclaimers are the honest
form and a `true` flag would not be. -/
theorem exhaustion_flag_is_free :
    ∃ p q : CoverageClaim, p.claimsSourceAgreement = q.claimsSourceAgreement ∧
      p.claimsExhaustiveCoverage ≠ q.claimsExhaustiveCoverage :=
  ⟨⟨true, false⟩, ⟨false, false⟩, rfl, by decide⟩

/-! ## The observer form -/

variable {Y Z : Type}

/-- The consumer is determined by the observation **on the declared carrier**:
states outside it are not compared. -/
def DeterminesOn (S : X → Prop) (O : X → Y) (C : X → Z) : Prop :=
  ∀ x y, S x → S y → O x = O y → C x = C y

/-- Global determination restricts. -/
theorem determinesOn_of_determines {S : X → Prop} {O : X → Y} {C : X → Z}
    (h : Determines O C) : DeterminesOn S O C := fun x y _ _ hxy => h x y hxy

/-- **And the restriction is strict.**  Parity is a sufficient observation for
the identity consumer on the two-element declared carrier and is not sufficient
on `ℕ`.  So a model that is complete in its own chart licenses nothing about the
exterior, even when its internal completeness proof is correct. -/
theorem determinesOn_not_determines :
    DeterminesOn declared (fun n : ℕ => n % 2) (fun n : ℕ => n) ∧
      ¬ Determines (fun n : ℕ => n % 2) (fun n : ℕ => n) := by
  constructor
  · intro x y hx hy hxy
    simp only [declared] at hx hy
    simp only at hxy ⊢
    omega
  · exact not_determines_of_collision (x₁ := 0) (x₂ := 2) rfl (by norm_num)

end Integration.DeclaredCarrier
