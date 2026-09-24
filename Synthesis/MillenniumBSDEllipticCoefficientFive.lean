import Synthesis.MillenniumBSDEtaEllipticFirstCoefficient
import Synthesis.MillenniumBSDGlobalEulerPrimePower
import Mathlib.Tactic

/-!
# The first nontrivial surviving elliptic coefficient: a_5 = -2

For E : y²=x³-x, the finite F₅ point count is literal and decidable.
The global coefficient at 5 is the k=1 local prime-power coefficient, hence
the already-proved local/global same-object theorem transports the computation
to the actual global L-series coefficient.
-/

namespace Synthesis.Millennium.BSD

instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

theorem cmProjectivePointCount_five :
    @projectivePointCount 5 inferInstance = 8 := by
  native_decide

theorem cmFrobeniusCoefficient_five :
    @frobeniusCoefficient 5 inferInstance = -2 := by
  norm_num [frobeniusCoefficient, cmProjectivePointCount_five]

theorem cmExplicitPrimePowerCoefficient_five_one :
    @explicitPrimePowerCoefficient 5 inferInstance 1 = -2 := by
  simp [explicitPrimePowerCoefficient, cmFrobeniusCoefficient_five]

theorem cmAllNCoefficient_five :
    cmAllNCoefficient 5 = -2 := by
  have h := cmAllNCoefficient_odd_primePower
    (p := 5) (by norm_num : (5 : ℕ) ≠ 2) 1
  norm_num [cmExplicitPrimePowerCoefficient_five_one] at h ⊢
  exact h

theorem cmEllipticCoefficientComplex_five :
    cmEllipticCoefficientComplex 5 = -2 := by
  simp [cmEllipticCoefficientComplex, cmAllNCoefficient_five]

end Synthesis.Millennium.BSD
