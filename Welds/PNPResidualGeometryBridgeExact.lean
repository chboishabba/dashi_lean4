import Welds.PNPLinearConsumerCutExact
import Welds.PNPTargetTrellisExact
import Welds.PNPInputOnlyChargeCeilingExact

namespace PNPResidualGeometryBridge
open PNPLinearConsumerCut PNPF3SyndromeBoundary

-- The fixed-anchor version of the global Boolean difference construction.
-- A displacement is admissible exactly when each coordinate is zero or
-- the signed move away from the original bit.
def LegalAt {n : Nat} (x : Fin n → Bool) (d : Syndrome n) : Prop :=
  ∀ i, d i = 0 ∨ d i = (if x i then 1 else 2)

def reopen {n : Nat} (x : Fin n → Bool) (d : Syndrome n) : Fin n → Bool :=
  fun i => if d i = 0 then x i else !x i

theorem anchored_legal {n : Nat} (x y : Fin n → Bool) :
    LegalAt x (boolEmbed x - boolEmbed y) := by
  intro i
  change boolEmbed x i - boolEmbed y i = 0 ∨
    boolEmbed x i - boolEmbed y i = (if x i then 1 else 2)
  cases hx : x i <;> cases hy : y i <;> simp [boolEmbed, hx, hy] <;> decide

theorem anchored_reopen {n : Nat} (x : Fin n → Bool) (d : Syndrome n)
    (h : LegalAt x d) : boolEmbed x - boolEmbed (reopen x d) = d := by
  funext i
  change boolEmbed x i - boolEmbed (reopen x d) i = d i
  rcases h i with hz | hs
  · simp [boolEmbed, reopen, hz]
  · cases hx : x i <;> simp [hx] at hs <;>
      simp [boolEmbed, reopen, hx, hs] <;> decide

-- Exact fixed-anchor linear obstruction. No claim about every input,
-- arbitrary implicit fibre discovery, or unrestricted computation.
theorem anchored_obstruction {n w m : Nat}
    (A : Syndrome n →ₗ[ZMod 3] Syndrome w)
    (B : Syndrome n →ₗ[ZMod 3] Syndrome m)
    (x : Fin n → Bool) (R : Finset (Fin n)) :
    (∃ y : Fin n → Bool, A (boolEmbed x) = A (boolEmbed y) ∧
      (∀ i ∈ R, x i = y i) ∧ B (boolEmbed x) ≠ B (boolEmbed y)) ↔
    (∃ d : Syndrome n, LegalAt x d ∧ A d = 0 ∧
      (∀ i ∈ R, d i = 0) ∧ B d ≠ 0) := by
  constructor
  · rintro ⟨y, ha, hr, hb⟩
    refine ⟨boolEmbed x - boolEmbed y, anchored_legal x y, ?_, ?_, ?_⟩
    · rw [map_sub, ha, sub_self]
    · intro i hi
      change boolEmbed x i - boolEmbed y i = 0
      simp [boolEmbed, hr i hi]
    · rw [map_sub]
      exact sub_ne_zero.mpr hb
  · rintro ⟨d, hd, ha, hr, hb⟩
    refine ⟨reopen x d, ?_, ?_, ?_⟩
    · apply sub_eq_zero.mp
      rw [← map_sub, anchored_reopen x d hd, ha]
    · intro i hi
      simp [reopen, hr i hi]
    · intro eq
      apply hb
      rw [← anchored_reopen x d hd, map_sub, eq, sub_self]

-- For arbitrary (even nonlinear) retained states and consumers, a
-- residual class is a sound quotient iff the consumer factors through it.
theorem consumer_factor_iff {X K Y : Type*}
    (key : X → K) (consumer : X → Y) :
    (∀ x y, key x = key y → consumer x = consumer y) ↔
    ∃ f : Set.range key → Y, ∀ x, f ⟨key x, ⟨x,rfl⟩⟩ = consumer x := by
  classical
  constructor
  · intro h
    let f : Set.range key → Y := fun k => consumer (Classical.choose k.property)
    refine ⟨f, ?_⟩
    intro x
    apply h
    exact Classical.choose_spec (show key x ∈ Set.range key from ⟨x,rfl⟩)
  · rintro ⟨f,h⟩ x y e
    have he : (⟨key x, ⟨x,rfl⟩⟩ : Set.range key) = ⟨key y, ⟨y,rfl⟩⟩ :=
      Subtype.ext e
    rw [← h x, ← h y, he]

-- The exact separator test is a hitting predicate on actual alternatives.
-- A dominated support imposes no additional obligation.
theorem dominated_support {I : Type*} (S T R : Set I) (h : S ⊆ T)
    (hit : ∃ i, i ∈ S ∧ i ∈ R) : ∃ i, i ∈ T ∧ i ∈ R := by
  rcases hit with ⟨i,hi,hr⟩
  exact ⟨i,h hi,hr⟩

end PNPResidualGeometryBridge
