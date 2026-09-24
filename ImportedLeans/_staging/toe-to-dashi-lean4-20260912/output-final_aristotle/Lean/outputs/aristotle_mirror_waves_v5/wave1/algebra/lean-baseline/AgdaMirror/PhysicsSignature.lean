import Mathlib
import AgdaMirror.MonsterOntos

/-!
# Lean mirror of `DASHI/Algebra/PhysicsSignature.agda` (genuine interface + lemmas)

Faithful transcription of the 15-bit "physics signature" scanner:

* `Sig15` — a 15-field boolean signature over the 15 supersingular primes,
* `State` — a minimal one-point physics state carrier,
* `Lens` — a per-prime compatibility detector `Compat : SSP → State → Bool`,
* `scan` — assembling the signature by scanning the lens over all 15 primes.

We reuse the `SSP` carrier already mirrored in `AgdaMirror.MonsterOntos`, and
additionally prove the genuine facts that the all-`true` lens scans to the
all-`true` signature and the all-`false` lens to the all-`false` signature.
No `sorry`, axiom-clean.
-/

namespace AgdaMirror.PhysicsSignature

open AgdaMirror.MonsterOntos
open SSP

/-- A 15-bit signature over the supersingular primes (Agda `record Sig15`). -/
structure Sig15 where
  b2 : Bool
  b3 : Bool
  b5 : Bool
  b7 : Bool
  b11 : Bool
  b13 : Bool
  b17 : Bool
  b19 : Bool
  b23 : Bool
  b29 : Bool
  b31 : Bool
  b41 : Bool
  b47 : Bool
  b59 : Bool
  b71 : Bool
  deriving DecidableEq, Repr

/-- Minimal one-point physics state (Agda `data State`). -/
inductive State | st deriving DecidableEq, Repr

/-- A per-prime compatibility detector (Agda `record Lens`). -/
structure Lens where
  Compat : SSP → State → Bool

/-- Scan the lens over all 15 primes to produce a signature (Agda `scan`). -/
def scan (L : Lens) (s : State) : Sig15 :=
  { b2 := L.Compat p2 s, b3 := L.Compat p3 s, b5 := L.Compat p5 s
    b7 := L.Compat p7 s, b11 := L.Compat p11 s, b13 := L.Compat p13 s
    b17 := L.Compat p17 s, b19 := L.Compat p19 s, b23 := L.Compat p23 s
    b29 := L.Compat p29 s, b31 := L.Compat p31 s, b41 := L.Compat p41 s
    b47 := L.Compat p47 s, b59 := L.Compat p59 s, b71 := L.Compat p71 s }

/-- The all-compatible lens. -/
def trueLens : Lens := ⟨fun _ _ => true⟩

/-- The never-compatible lens. -/
def falseLens : Lens := ⟨fun _ _ => false⟩

/-- The all-`true` signature. -/
def fullSig : Sig15 :=
  ⟨true, true, true, true, true, true, true, true, true, true, true, true, true, true, true⟩

/-- The all-`false` signature. -/
def emptySig : Sig15 :=
  ⟨false, false, false, false, false, false, false, false, false, false, false, false, false, false, false⟩

/-- Scanning the all-compatible lens yields the full signature. -/
theorem scan_trueLens (s : State) : scan trueLens s = fullSig := by
  cases s; rfl

/-- Scanning the never-compatible lens yields the empty signature. -/
theorem scan_falseLens (s : State) : scan falseLens s = emptySig := by
  cases s; rfl

end AgdaMirror.PhysicsSignature
