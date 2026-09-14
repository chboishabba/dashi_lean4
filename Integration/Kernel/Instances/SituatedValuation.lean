import Integration.Kernel.Quotient

/-!
# A symbolic instance: situated valuation and the inverse firewall

The contextual-semantics lane of the corpus
(`Agda/DASHI/Cognition/PNF/ContextualFractran*Exact.agda`) replaces a static
`(word, part-of-speech) ↦ value` dictionary by a valuation attached to a *token
occurrence in a world and a query frame*, and insists that the arithmetic
inverse of a value (there: a reciprocal) is only a **candidate**
transformation until a semantic gate authorises it.  In the Agda snapshot both
points appear as pointwise `refl` equations plus `Bool`-valued boundary records.
Here they are theorems.

## What is proved

* **`no_static_lexicon`** — no function of `(word, part of speech)` reproduces
  the situated valuation: the same word in the same grammatical role takes
  different values in different worlds.  This is
  `Quotient.not_descendsThrough_of_collision` for the lexical quotient.
* `situated_descends_through_full_context` — with the world restored the
  valuation does descend, so the failure is exactly the missing coordinate and
  nothing else.
* `world_strictly_refines_lexicon`, `lexicon_still_correct` — adding the world
  coordinate is a strict refinement of the lexical observation, under which the
  lexical reading itself remains correct.
* **`flip_is_an_ambient_inverse`** — reversing the oriented relation role
  inverts the value in `ℚ`, unconditionally: the arithmetic always works.
* **`ambient_inverse_is_not_lawful`** — and yet there is an occurrence at which
  the reversal is *not* admissible, so the arithmetic inverse is not a semantic
  inverse.  `lawfulFlip_is_ambient` records the one-way implication, and
  `lawful_flip_exists` that the gate is not vacuous.
* `gate_does_not_descend_through_valuation` — admissibility is not a function of
  the value either: the firewall is not a property of the arithmetic.

**Claim boundary.** A "word" is one of two labels, a "world" one of two, and a
valuation is a positive rational. Nothing here models a language, a document, a
parser, or the FRACTRAN computation model; what is formalised is the
quotient/refinement and gating structure the lane states.
-/

namespace Integration.Kernel.Instances.SituatedValuation

open Integration.Kernel.Quotient

/-! ## §1 Occurrences -/

/-- Two labelled words. -/
inductive Word
  /-- A word whose reading depends on the world. -/
  | ambiguous
  /-- A word with a single reading. -/
  | fixed
  deriving DecidableEq, Fintype, Repr

/-- Two grammatical roles. -/
inductive POS
  /-- Nominal use. -/
  | noun
  /-- Verbal use. -/
  | verb
  deriving DecidableEq, Fintype, Repr

/-- Two worlds the same token can occur in. -/
inductive World
  /-- First world. -/
  | w₁
  /-- Second world. -/
  | w₂
  deriving DecidableEq, Fintype, Repr

/-- The orientation of the relation the occurrence participates in. -/
inductive Role
  /-- The relation read forwards. -/
  | forward
  /-- The relation read backwards. -/
  | reverse
  deriving DecidableEq, Fintype, Repr

/-- A token occurrence: a word used in a grammatical role, in a world, in a
relation orientation, with or without an admissible bracket for reversal. -/
structure Occurrence where
  /-- The word. -/
  word : Word
  /-- Its grammatical role. -/
  pos : POS
  /-- The world of the occurrence. -/
  world : World
  /-- The orientation of the relation. -/
  role : Role
  /-- Whether a bracket authorising reversal is available here. -/
  bracket : Bool
  deriving DecidableEq, Repr

/-- What a static dictionary can see. -/
def lexical (o : Occurrence) : Word × POS := (o.word, o.pos)

/-- The prime-style code of a word in a world: the `ambiguous` word takes
different codes in the two worlds. -/
def code : Word → World → ℚ
  | Word.ambiguous, World.w₁ => 2
  | Word.ambiguous, World.w₂ => 3
  | Word.fixed, _ => 5

theorem code_pos (w : Word) (v : World) : 0 < code w v := by
  cases w <;> cases v <;> norm_num [code]

theorem code_ne_zero (w : Word) (v : World) : code w v ≠ 0 := (code_pos w v).ne'

/-- The situated valuation: the world-dependent code, inverted when the relation
is read backwards. -/
def valuation (o : Occurrence) : ℚ :=
  match o.role with
  | Role.forward => code o.word o.world
  | Role.reverse => (code o.word o.world)⁻¹

theorem valuation_ne_zero (o : Occurrence) : valuation o ≠ 0 := by
  cases h : o.role <;> simp [valuation, h, code_ne_zero]

/-! ## §2 A static lexicon cannot reproduce the situated valuation -/

/-- The same word, same part of speech, same orientation — in the two worlds. -/
def inW₁ : Occurrence := ⟨Word.ambiguous, POS.noun, World.w₁, Role.forward, true⟩

/-- The same occurrence read in the second world. -/
def inW₂ : Occurrence := ⟨Word.ambiguous, POS.noun, World.w₂, Role.forward, true⟩

theorem lexical_collides : lexical inW₁ = lexical inW₂ := rfl

theorem valuation_separates : valuation inW₁ ≠ valuation inW₂ := by
  norm_num [valuation, inW₁, inW₂, code]

/-- **No static `(word, part of speech)` dictionary computes the situated
valuation.** -/
theorem no_static_lexicon : ¬ DescendsThrough valuation lexical :=
  not_descendsThrough_of_collision lexical_collides valuation_separates

/-- With the world restored, the valuation does descend: the obstruction is
exactly the missing coordinate. -/
theorem situated_descends_through_full_context :
    DescendsThrough valuation (fun o => (o.word, o.world, o.role)) := by
  refine ⟨fun t => match t.2.2 with
    | Role.forward => code t.1 t.2.1
    | Role.reverse => (code t.1 t.2.1)⁻¹, fun o => ?_⟩
  cases h : o.role <;> simp [valuation, h]

/-- Reading the world strictly refines the lexical observation. -/
theorem world_strictly_refines_lexicon :
    StrictlyRefines lexical (pair lexical Occurrence.world) :=
  strictlyRefines_pair_of_separates lexical Occurrence.world lexical_collides (by decide)

/-- …and the lexical reading remains a correct function of the refined one. -/
theorem lexicon_still_correct : DescendsThrough lexical (pair lexical Occurrence.world) :=
  refinement_is_not_refutation lexical Occurrence.world

/-! ## §3 The inverse firewall -/

/-- Reversing the orientation of the relation. -/
def flip (o : Occurrence) : Occurrence :=
  { o with role := match o.role with
      | Role.forward => Role.reverse
      | Role.reverse => Role.forward }

/-- **The arithmetic always works**: flipping the orientation inverts the value
in `ℚ`, at every occurrence. -/
theorem flip_is_an_ambient_inverse (o : Occurrence) : valuation (flip o) = (valuation o)⁻¹ := by
  cases h : o.role <;>
    simp [valuation, flip, h, inv_inv]

theorem flip_involutive (o : Occurrence) : flip (flip o) = o := by
  cases o with
  | mk word pos world role bracket => cases role <;> rfl

/-- The semantic gate: reversal is admissible only where a bracket is available. -/
def Admits (o : Occurrence) : Prop := o.bracket = true

instance (o : Occurrence) : Decidable (Admits o) := by unfold Admits; infer_instance

/-- A lawful reversal is an admissible one that also inverts the value. -/
def LawfulFlip (o : Occurrence) : Prop := Admits o ∧ valuation (flip o) = (valuation o)⁻¹

theorem lawfulFlip_is_ambient {o : Occurrence} (h : LawfulFlip o) :
    valuation (flip o) = (valuation o)⁻¹ := h.2

theorem lawful_flip_exists : LawfulFlip inW₁ := ⟨rfl, flip_is_an_ambient_inverse inW₁⟩

/-- An occurrence with no bracket available. -/
def unbracketed : Occurrence := ⟨Word.ambiguous, POS.noun, World.w₁, Role.forward, false⟩

/-- **The ambient arithmetic inverse is not a lawful semantic inverse.**  At
`unbracketed` the reciprocal is available and the gate refuses it. -/
theorem ambient_inverse_is_not_lawful :
    valuation (flip unbracketed) = (valuation unbracketed)⁻¹ ∧ ¬ LawfulFlip unbracketed :=
  ⟨flip_is_an_ambient_inverse unbracketed, fun h => by simpa [Admits, unbracketed] using h.1⟩

/-- Admissibility is not a function of the value: two occurrences with the same
valuation differ on the gate, so the firewall cannot be read off the
arithmetic. -/
theorem gate_does_not_descend_through_valuation :
    ¬ DescendsThrough (fun o => decide (Admits o)) valuation := by
  refine not_descendsThrough_of_collision (x := inW₁) (y := unbracketed) rfl ?_
  decide

end Integration.Kernel.Instances.SituatedValuation
