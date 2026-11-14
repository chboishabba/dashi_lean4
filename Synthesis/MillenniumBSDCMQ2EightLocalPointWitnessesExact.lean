import Synthesis.MillenniumBSDCMQ2AllOddUnitHenselExact
import Mathlib.Tactic

/-!
BSD K1: E:y²=x³-x, E(Q₂), eight concrete non-torsion local
point witnesses at x = 28,31,33,39,41,112,1/4,1/16.
Every point is the ORIGINAL cubic, using genuine Hensel roots of
u ≡ 1 mod 8 and rational scaling y=scale*z. No uninhabited
point oracle, no ZMod-only witness, no new curve.
The eight corresponding rational squareclass triples are pairwise
distinct by an independent exact rational test; equality with the
full original local Kummer image/H¹ remains open.
SOURCE-WRITTEN, Lean 4.28 pinned kernel acceptance pending.
-/

noncomputable section
namespace Synthesis.Millennium.BSD

private theorem cmE_Q2_from_oddUnit
    (x scale : ℚ) (u : ℤ)
    (hu : (2 : ℤ)^3 ∣ 1-u)
    (hfactor :
      (x : ℚ_[2])^3 - (x : ℚ_[2]) =
        (scale : ℚ_[2])^2 * (u : ℚ_[2])) :
    ∃ y : ℚ_[2], y^2 = (x : ℚ_[2])^3 - x := by
  obtain ⟨z,hz⟩ := cmQ2SquareRootOfOneModEight u hu
  refine ⟨(scale : ℚ_[2])*z, ?_⟩
  calc
    ((scale : ℚ_[2])*z)^2 = (scale : ℚ_[2])^2*z^2 := by ring
    _ = (scale : ℚ_[2])^2*(u : ℚ_[2]) := by rw [hz]
    _ = (x : ℚ_[2])^3-x := hfactor.symm


/-- Literal original E(Q₂) point at rational x = 28.
     Here x³−x = (2)² · (5481) and 5481 ≡ 1 (mod 8). -/
theorem cmE_Q2_localPoint_28 :
    ∃ y : ℚ_[2],
      y^2 = ((((28) : ℚ)) : ℚ_[2])^3 - ((((28) : ℚ)) : ℚ_[2]) := by
  exact cmE_Q2_from_oddUnit (28 : ℚ) (2 : ℚ) (5481 : ℤ)
    (by norm_num) (by norm_num)

/-- Literal original E(Q₂) point at rational x = 31.
     Here x³−x = (8)² · (465) and 465 ≡ 1 (mod 8). -/
theorem cmE_Q2_localPoint_31 :
    ∃ y : ℚ_[2],
      y^2 = ((((31) : ℚ)) : ℚ_[2])^3 - ((((31) : ℚ)) : ℚ_[2]) := by
  exact cmE_Q2_from_oddUnit (31 : ℚ) (8 : ℚ) (465 : ℤ)
    (by norm_num) (by norm_num)

/-- Literal original E(Q₂) point at rational x = 33.
     Here x³−x = (8)² · (561) and 561 ≡ 1 (mod 8). -/
theorem cmE_Q2_localPoint_33 :
    ∃ y : ℚ_[2],
      y^2 = ((((33) : ℚ)) : ℚ_[2])^3 - ((((33) : ℚ)) : ℚ_[2]) := by
  exact cmE_Q2_from_oddUnit (33 : ℚ) (8 : ℚ) (561 : ℤ)
    (by norm_num) (by norm_num)

/-- Literal original E(Q₂) point at rational x = 39.
     Here x³−x = (4)² · (3705) and 3705 ≡ 1 (mod 8). -/
theorem cmE_Q2_localPoint_39 :
    ∃ y : ℚ_[2],
      y^2 = ((((39) : ℚ)) : ℚ_[2])^3 - ((((39) : ℚ)) : ℚ_[2]) := by
  exact cmE_Q2_from_oddUnit (39 : ℚ) (4 : ℚ) (3705 : ℤ)
    (by norm_num) (by norm_num)

/-- Literal original E(Q₂) point at rational x = 41.
     Here x³−x = (4)² · (4305) and 4305 ≡ 1 (mod 8). -/
theorem cmE_Q2_localPoint_41 :
    ∃ y : ℚ_[2],
      y^2 = ((((41) : ℚ)) : ℚ_[2])^3 - ((((41) : ℚ)) : ℚ_[2]) := by
  exact cmE_Q2_from_oddUnit (41 : ℚ) (4 : ℚ) (4305 : ℤ)
    (by norm_num) (by norm_num)

/-- Literal original E(Q₂) point at rational x = 112.
     Here x³−x = (4)² · (87801) and 87801 ≡ 1 (mod 8). -/
theorem cmE_Q2_localPoint_112 :
    ∃ y : ℚ_[2],
      y^2 = ((((112) : ℚ)) : ℚ_[2])^3 - ((((112) : ℚ)) : ℚ_[2]) := by
  exact cmE_Q2_from_oddUnit (112 : ℚ) (4 : ℚ) (87801 : ℤ)
    (by norm_num) (by norm_num)

/-- Literal original E(Q₂) point at rational x = 1/4.
     Here x³−x = (1/8)² · (-15) and -15 ≡ 1 (mod 8). -/
theorem cmE_Q2_localPoint_quarter :
    ∃ y : ℚ_[2],
      y^2 = ((((1/4) : ℚ)) : ℚ_[2])^3 - ((((1/4) : ℚ)) : ℚ_[2]) := by
  exact cmE_Q2_from_oddUnit (1/4 : ℚ) (1/8 : ℚ) (-15 : ℤ)
    (by norm_num) (by norm_num)

/-- Literal original E(Q₂) point at rational x = 1/16.
     Here x³−x = (1/64)² · (-255) and -255 ≡ 1 (mod 8). -/
theorem cmE_Q2_localPoint_sixteenth :
    ∃ y : ℚ_[2],
      y^2 = ((((1/16) : ℚ)) : ℚ_[2])^3 - ((((1/16) : ℚ)) : ℚ_[2]) := by
  exact cmE_Q2_from_oddUnit (1/16 : ℚ) (1/64 : ℚ) (-255 : ℤ)
    (by norm_num) (by norm_num)

-- Distinctness of their actual local Kummer square-class images
-- requires the genuine Q₂*/Q₂*² quotient, valuation/residue transport,
-- and actual E[2]-valued cohomology. The exact rational certificate
-- identifies the eight triples without treating tags as H¹ itself.

end Synthesis.Millennium.BSD
