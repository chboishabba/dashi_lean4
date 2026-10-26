import Mathlib

/-!
# Witten 1989 CS–WZW vs Witten 2007 Monster/AdS3: type-safe finite cut

Prior source owners: Witten 1989, Verlinde, FLM, Witten 2007,
Maloney--Witten 2007. Existing Agda source: SU2Level4Spin1RepReceipt,
KacMoodyLevelReceipt and the Monster c24 Virasoro/AdS3 PR #1239.
The finite fusion-rule formula is the published SU2_k truncation for k=4.
It is NOT a Lie-group/affine VOA construction or proof of the
1989 CS/WZW path integral or the speculative 2007 3D gravity dual.
-/
namespace DASHIWittenCSWZW

/-- Doubled spins a,b,c in {0,1,2,3,4} for SU(2)_4. -/
def fusion (a b c : Fin 5) : ℕ :=
  if (a.val + b.val + c.val) % 2 = 0 ∧
     Nat.dist a.val b.val ≤ c.val ∧
     c.val ≤ min (a.val + b.val) (8 - a.val - b.val)
  then 1 else 0

/-- Actual k4 fusion rule; all 125 triples are source-governed finite data.
Associativity concerns these chosen fusion coefficients, not a completed
physical Chern–Simons Hilbert space. -/
theorem fusionAssociative :
    ∀ a b c d : Fin 5,
      (∑ x : Fin 5, fusion a b x * fusion x c d) =
      (∑ x : Fin 5, fusion b c x * fusion a x d) := by
  decide

/-- One precise truncated quantum SU2 rule: 1 ⊗ 1 = 0 ⊕ 2. -/
theorem selectedFusion11 : fusion 1 1 0 = 1 ∧
    fusion 1 1 2 = 1 ∧ fusion 1 1 4 = 0 := by decide

/-- The SU2 k4 simple-current has fusion 4 ⊗ 4 = 0. -/
theorem selectedFusion44 : fusion 4 4 0 = 1 ∧
    fusion 4 4 2 = 0 ∧ fusion 4 4 4 = 0 := by decide

/-- Quantum dimensions from SU2_4 exact source: (1,√3,2,√3,1). -/
theorem squaredQuantumDimensions : (1:ℕ) + 3 + 4 + 3 + 1 = 12 := by norm_num

/-- Witten's 1989 SU2_4 torus CS conformal-block basis has 5 primaries.
The FLM Monster holomorphic c24 chiral VOA has just one irreducible module.
This is a sourced representation-count NO-GO, not an AdS3 bulk theorem. -/
theorem noDirectChiralBlockIdentification : (5:ℕ) ≠ 1 := by norm_num

/-- The SU2_4 chiral central charge is c=3k/(k+2)=2, whereas the
Monster CFT chiral central charge is c=24. -/
theorem sourceCentralChargeMismatch :
    (3*(4:ℚ)/(4+2) : ℚ) = 2 ∧ (2:ℚ) ≠ 24 := by norm_num

/-- At the level of modular tensor category framing, SU2_4 has
Gauss-Milgram phase i, whereas a holomorphic c24 category has phase 1.
The actual CFT Gauss sum is externally specified, not derived here. -/
theorem sourceFramingAnomalyMismatch : (Complex.I : ℂ) ≠ 1 := by simp

end DASHIWittenCSWZW
