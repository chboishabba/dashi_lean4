import Synthesis.MonsterCyclotomicCharacterRecognition
import Synthesis.MonsterCentralProjectorSplit

/-!
# Actual parity character cut

A central involution on the derived actual multiplicity action gives its
negative and positive blocks. The trace cut is derived on those actual
blocks, using trace conjugacy, not inferred from their dimensions.
The proof of the literal parity split is an upstream projector obligation.
-/
namespace Synthesis.MonsterActualParityCharacter
noncomputable section
universe u
variable {k G V M P : Type u}
variable [Field k] [CharZero k] [Group G]
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]
variable [AddCommGroup M] [Module k M] [FiniteDimensional k M]
variable [AddCommGroup P] [Module k P] [FiniteDimensional k P]
variable (rho : Representation k G V)
variable (minus : Representation k G M) (plus : Representation k G P)

/-- The split identifies the actual action, including its marked central
involution. The ordinary source representations are not used to define it. -/
structure ParitySplit where
  split : V ≃ₗ[k] (M × P)
  j : G
  action : ∀ g, split.conj (rho g) = LinearMap.prodMap (minus g) (plus g)
  negative : minus j = -1
  positive : plus j = 1

variable (D : ParitySplit rho minus plus)

theorem traceSum (g : G) :
    LinearMap.trace k V (rho g) =
      LinearMap.trace k M (minus g) + LinearMap.trace k P (plus g) := by
  rw [← LinearMap.trace_conj' (rho g) D.split, D.action,
    LinearMap.trace_prodMap']

theorem traceTwist (g : G) :
    LinearMap.trace k V (rho (g * D.j)) =
      -LinearMap.trace k M (minus g) + LinearMap.trace k P (plus g) := by
  simp only [traceSum rho minus plus D, map_mul, D.negative, D.positive,
    mul_neg, mul_one, map_neg]

theorem negativeTrace (g : G) :
    LinearMap.trace k M (minus g) =
      (LinearMap.trace k V (rho g) -
        LinearMap.trace k V (rho (g * D.j))) / 2 := by
  rw [traceSum rho minus plus D, traceTwist rho minus plus D]
  ring

theorem positiveTrace (g : G) :
    LinearMap.trace k P (plus g) =
      (LinearMap.trace k V (rho g) +
        LinearMap.trace k V (rho (g * D.j))) / 2 := by
  rw [traceSum rho minus plus D, traceTwist rho minus plus D]
  ring

/-- The entire same-object character sum plus the original marked central
signs determines BOTH block characters, without a second native trace run. -/
theorem blockCharacterOfSum (a b : G → k)
    (h : ∀ g, LinearMap.trace k V (rho g) = a g + b g)
    (ha : ∀ g, a (g * D.j) = -a g)
    (hb : ∀ g, b (g * D.j) = b g) :
    (∀ g, LinearMap.trace k M (minus g) = a g) ∧
    (∀ g, LinearMap.trace k P (plus g) = b g) := by
  constructor
  · intro g
    rw [negativeTrace rho minus plus D, h g, h (g * D.j), ha, hb]
    ring
  · intro g
    rw [positiveTrace rho minus plus D, h g, h (g * D.j), ha, hb]
    ring

/-- The standard FDRep of the actual operator has literally the same trace. -/
theorem characterActual (g : G) :
    (FDRep.of rho).character g = LinearMap.trace k V (rho g) := rfl

section Recognition
open Synthesis.MonsterCyclotomicCharacterRecognition
variable [Fintype G] [Invertible (Fintype.card G : k)]
variable [Invertible (Nat.card G : k)] [NeZero (Nat.card G : k)]

theorem ordinaryBlocks (T12 T78 : FDRep k G)
    (n12 : pairing T12.character T12.character = 1)
    (n78 : pairing T78.character T78.character = 1)
    (h : ∀ g, LinearMap.trace k V (rho g) = T12.character g + T78.character g)
    (ha : ∀ g, T12.character (g * D.j) = -T12.character g)
    (hb : ∀ g, T78.character (g * D.j) = T78.character g) :
    Nonempty (T12 ≅ FDRep.of minus) ∧ Nonempty (T78 ≅ FDRep.of plus) := by
  obtain ⟨h12,h78⟩ := blockCharacterOfSum rho minus plus D
    T12.character T78.character h ha hb
  exact twoBlocks (FDRep.of minus) (FDRep.of plus) T12 T78 n12 n78
    (funext h12) (funext h78)

end Recognition
end
end Synthesis.MonsterActualParityCharacter
