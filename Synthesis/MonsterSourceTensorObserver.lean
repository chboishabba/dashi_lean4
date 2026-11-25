import Synthesis.MonsterProjectedOriginalCharacter

/-!
# Original BW source model: rank-one observer trace

Source-side counterpart of the original Conway compression. Once the
marked original source row is realized as the paired tensor representation,
the joint phase/vacuum observer kills the complementary phase and original
zero residual and is rank one on the common Heisenberg factor.
The trace is then forced by Mathlib trace_smulRight, trace_tensorProduct'
and trace_prodMap', not a separately stipulated 90D character.
Source-written, kernel not run.
-/
namespace Synthesis.MonsterSourceTensorObserver
noncomputable section
open scoped TensorProduct
universe u
variable {k H A B R : Type u} [Field k]
variable [AddCommGroup H] [Module k H] [FiniteDimensional k H]
variable [AddCommGroup A] [Module k A] [FiniteDimensional k A]
variable [AddCommGroup B] [Module k B] [FiniteDimensional k B]
variable [AddCommGroup R] [Module k R] [FiniteDimensional k R]

/-- The marked source vacuum projection composed with the Weil operator.
The same factor occurs on both original source constituents. -/
def compressedWeil (ell : H →ₗ[k] k) (v : H) (K : H →ₗ[k] H) : H →ₗ[k] H :=
  (ell.comp K).smulRight v

theorem compressedWeilTrace (ell : H →ₗ[k] k) (v : H) (K : H →ₗ[k] H) :
    LinearMap.trace k H (compressedWeil ell v K) = ell (K v) := by
  rw [compressedWeil, LinearMap.trace_smulRight]
  rfl

/-- Here R includes the untouched original zero phase and opposite marked
phase. It is killed by this observer, not discarded from the actual module. -/
def sourceBlockOperator (ell : H →ₗ[k] k) (v : H) (K : H →ₗ[k] H)
    (a : A →ₗ[k] A) (b : B →ₗ[k] B) :
    (R × ((H ⊗[k] A) × (H ⊗[k] B))) →ₗ[k]
      (R × ((H ⊗[k] A) × (H ⊗[k] B))) :=
  LinearMap.prodMap 0 (LinearMap.prodMap
    (TensorProduct.map (compressedWeil ell v K) a)
    (TensorProduct.map (compressedWeil ell v K) b))

theorem sourceBlockTrace (ell : H →ₗ[k] k) (v : H) (K : H →ₗ[k] H)
    (a : A →ₗ[k] A) (b : B →ₗ[k] B) :
    LinearMap.trace k (R × ((H ⊗[k] A) × (H ⊗[k] B)))
      (sourceBlockOperator ell v K a b) =
    ell (K v) * (LinearMap.trace k A a + LinearMap.trace k B b) := by
  simp only [sourceBlockOperator, LinearMap.trace_prodMap', map_zero,
    zero_add, LinearMap.trace_tensorProduct', compressedWeilTrace]
  ring

/-- A literal source model may be in a different basis. Transport the
projected operator by an actual linear equivalence and take the same trace. -/
theorem sourceTraceInOriginalBasis {V : Type u}
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (e : V ≃ₗ[k] (R × ((H ⊗[k] A) × (H ⊗[k] B))))
    (op : V →ₗ[k] V)
    (ell : H →ₗ[k] k) (v : H) (K : H →ₗ[k] H)
    (a : A →ₗ[k] A) (b : B →ₗ[k] B)
    (h : e.conj op = sourceBlockOperator ell v K a b) :
    LinearMap.trace k V op =
      ell (K v) * (LinearMap.trace k A a + LinearMap.trace k B b) := by
  rw [← LinearMap.trace_conj' op e, h, sourceBlockTrace]

end
end Synthesis.MonsterSourceTensorObserver
