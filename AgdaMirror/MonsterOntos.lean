import Mathlib

/-!
# Lean mirror of `MonsterOntos.agda` (genuine, fully proved)

Faithful transcription of `MonsterOntos.agda`: the 15 supersingular primes
dividing `|M|` as a carrier type `SSP`, the embedding `toNat`, its injectivity,
and decidable equality (derived).  All genuine, fully proved.
-/

namespace AgdaMirror.MonsterOntos

/-- The 15 supersingular primes used as the base carrier. -/
inductive SSP where
  | p2 | p3 | p5 | p7 | p11 | p13 | p17 | p19 | p23 | p29 | p31 | p41 | p47 | p59 | p71
  deriving DecidableEq

open SSP

/-- Concrete embedding to `Nat`. -/
def toNat : SSP → Nat
  | p2 => 2 | p3 => 3 | p5 => 5 | p7 => 7 | p11 => 11 | p13 => 13 | p17 => 17
  | p19 => 19 | p23 => 23 | p29 => 29 | p31 => 31 | p41 => 41 | p47 => 47
  | p59 => 59 | p71 => 71

/-- `toNat` is injective: each prime maps to a unique `Nat`. -/
theorem toNat_injective : ∀ {p q : SSP}, toNat p = toNat q → p = q := by
  intro p q h; cases p <;> cases q <;> simp_all [toNat]

end AgdaMirror.MonsterOntos
