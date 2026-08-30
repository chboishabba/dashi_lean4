import Mathlib

/-!
# Lean mirror of `SWAR_Equivalence.agda` (genuine *conditional* content, fully proved)

Faithful transcription of `SWAR_Equivalence.agda`.  The Agda module postulates an
abstract packed representation (`Packed`, `pack`, `unpack`, `swarXOR`) and the two
laws it needs — a section/retraction law (`unpack ∘ pack = id`) and a refinement
law (`swarXOR` simulates the lane-wise XOR through `unpack`) — bundled in a
record `SWARCorrect`, then *derives* correctness of `swarXOR` on packed vectors.

Honesty boundary: the Agda original uses `postulate` for the carriers and laws,
i.e. they are *assumed*, not established.  We mirror that honestly by abstracting
the carriers as section variables and bundling the two laws as fields of a
`SWARCorrect` structure (a hypothesis), with **no axioms**.  The derived lemma
`swar_correct_on_packed` is then genuinely proved from that hypothesis.
-/

namespace AgdaMirror.SWAR

section

variable {Code : Type} {Packed : Nat → Type}
variable (cxor : Code → Code → Code)

/-- Lane-wise reference operation. -/
def laneXOR {n : Nat} (x y : List.Vector Code n) : List.Vector Code n :=
  List.Vector.zipWith cxor x y

variable (pack : {n : Nat} → List.Vector Code n → Packed n)
variable (unpack : {n : Nat} → Packed n → List.Vector Code n)
variable (swarXOR : {n : Nat} → Packed n → Packed n → Packed n)

/-- The only thing needed to trust the SWAR fast path: a bisimulation/refinement
law together with the section/retraction law.  (Assumed, exactly as the Agda
`record SWARCorrect` postulated its fields.) -/
structure SWARCorrect where
  /-- `pack`/`unpack` are section/retraction on the domain of interest. -/
  unpack_pack : ∀ {n : Nat} (v : List.Vector Code n), unpack (pack v) = v
  /-- `swarXOR` refines `laneXOR` through `unpack`. -/
  swar_sound : ∀ {n : Nat} (x y : Packed n),
    unpack (swarXOR x y) = laneXOR cxor (unpack x) (unpack y)

/-- Derived: `swarXOR` is correct on packed values built from vectors. -/
theorem swar_correct_on_packed (C : SWARCorrect cxor pack unpack swarXOR)
    {n : Nat} (vx vy : List.Vector Code n) :
    unpack (swarXOR (pack vx) (pack vy)) = laneXOR cxor vx vy := by
  rw [C.swar_sound, C.unpack_pack, C.unpack_pack]

end

end AgdaMirror.SWAR
