import Integration.Paper9UniversalMatrixSymmetry
import Integration.Paper9IntegerSectorWeld

/-! Source-written, kernel pending. Exact residuals, not hashes.
The finite integer certificates are explicit premises. Once supplied at
the 42 signed integer nodes they determine the entire original matrix. -/
namespace Integration.Paper9SignedIntegerMatrixWeld
open Polynomial Complex UpperHalfPlane
open scoped BigOperators
open Integration.Paper9SignedUniversalMatrix
open Integration.Paper9UniversalMatrixSymmetry
open Integration.Paper9UniversalMonicSlice
open Integration.Paper9CyclotomicPacketReflection
open Integration.Paper9HeckeProductAssembly
open Integration.Paper9IntegerSectorWeld
open Integration.Paper9Hecke41ChartGeometry
noncomputable section
local notation "j" => Integration.MoonshineEisensteinAgdaTarget.jTarget

def intRow (c : ℕ → ℕ → ℤ) (k : ℕ) : Polynomial ℂ :=
  ∑ n ∈ Finset.range 43, C (c k n : ℂ)*X^n

theorem intRowDegree (c : ℕ → ℕ → ℤ) (k : ℕ) :
    (intRow c k).natDegree≤42 := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  unfold intRow
  rw [Polynomial.finset_sum_coeff]
  apply Finset.sum_eq_zero
  intro i hi
  have hi' := Finset.mem_range.mp hi
  simp [Polynomial.coeff_C_mul_X_pow,show i≠n by omega,show n≠i by omega]

theorem intRowCoeff (c : ℕ → ℕ → ℤ) (k n : ℕ) (hn : n≤42) :
    (intRow c k).coeff n=(c k n : ℂ) := by
  unfold intRow
  rw [Polynomial.finset_sum_coeff,Finset.sum_eq_single n]
  · simp [Polynomial.coeff_C_mul_X_pow]
  · intro i hi hne
    simp [Polynomial.coeff_C_mul_X_pow,hne,Ne.symm hne]
  · intro h
    exact (h (Finset.mem_range.mpr (by omega))).elim

def nodeCoeff (c : ℕ → ℕ → ℤ) (y : ℂ) (k : ℕ) : ℂ :=
  (intRow c k).eval y

-- Reuse integerNormCast and finite multiplication transport. Only the
-- finite original J stream casts and exact integer residuals are inputs.
structure NodeGate (c : ℕ → ℕ → ℤ) (y : ℤ) where
  H L N G B : Polynomial ℤ
  hH : H.coeff 0=1
  hL : L.coeff 0=0
  hN : N.coeff 0=1
  hlog : X^(41*42+1) ∣ eulerZ H-H*L
  hnorm : X^(42+1) ∣ eulerZ N-N*Polynomial.contract 41 L
  hcolumn : X^(42+1) ∣ G*N-B
  hHread : castPoly H=sliceH 1722 (y:ℂ)
  hGread : castPoly G=sliceInfinityQ 1722 (y:ℂ)
  hBread : castPoly B=columnQ 1722 42 (nodeCoeff c (y:ℂ))

theorem nodeResidual (c : ℕ → ℕ → ℤ) (y : ℤ) (g : NodeGate c y) :
    ∀ n≤42, (target (y:ℂ)-columnQ 1722 42 (nodeCoeff c (y:ℂ))).coeff n=0 := by
  intro n hn
  have hN := integerNormCast g.H g.L g.N 42 g.hH g.hL g.hN g.hlog g.hnorm
  have hP := mulCoeffTransport 42 (castPoly g.G) _ _ hN n hn
  have hB := integerColumnResidual 42 g.G g.N g.B g.hcolumn n hn
  rw [g.hHread,g.hGread] at hP
  rw [g.hGread,g.hBread] at hB
  rw [target,Polynomial.coeff_sub,hP]
  exact hB

-- Unit triangular pivot gives coefficient uniqueness without analytic
-- interpolation at each node. The analytic theorem is used only once
-- for degree and actual monic coefficient.
theorem nodeRows (c : ℕ → ℕ → ℤ) (y : ℤ) (g : NodeGate c y)
    (k : ℕ) (hk : k≤42) : nodeCoeff c (y:ℂ) k=(rows k).eval (y:ℂ) := by
  rw [rowsRead _ _ hk]
  induction k using Nat.strong_induction_on with
  | h k ih =>
    have h₁ := nodeResidual c y g k hk
    have h₂ := sliceResidual (y:ℂ) k hk
    rw [Polynomial.coeff_sub,columnQCoeff _ _ _ _ hk,
      Finset.sum_range_succ,pivotOne _ (jPolyZero 1722),mul_one] at h₁ h₂
    have hs : (∑ i ∈ Finset.range k, nodeCoeff c (y:ℂ) i*pivot (jPoly 1722) 42 k i)=
        ∑ i ∈ Finset.range k, sliceC (y:ℂ) i*pivot (jPoly 1722) 42 k i := by
      apply Finset.sum_congr rfl
      intro i hi
      have hlt := Finset.mem_range.mp hi
      rw [ih i hlt (by omega)]
    rw [hs] at h₁
    linear_combination h₂-h₁

structure SignedMatrixGate (c : ℕ → ℕ → ℤ) where
  leading : ∀ k≤42, c k 42=if k=42 then 1 else 0
  positive : ∀ i : Fin 21, NodeGate c ((i.val:ℤ)+1)
  negative : ∀ i : Fin 21, NodeGate c (-((i.val:ℤ)+1))

theorem integerRowExact (c : ℕ → ℕ → ℤ) (g : SignedMatrixGate c)
    (k : ℕ) (hk : k≤42) : intRow c k=rows k := by
  apply rowFromSigned k hk _ (intRowDegree c k)
  · rw [intRowCoeff c k 42 le_rfl,rowLeading k hk,g.leading k hk]
    split <;> simp_all
  · intro i
    constructor
    · simpa [nodeCoeff] using nodeRows c ((i.val:ℤ)+1) (g.positive i) k hk
    · simpa [nodeCoeff] using nodeRows c (-((i.val:ℤ)+1)) (g.negative i) k hk

theorem integerMatrixActual (c : ℕ → ℕ → ℤ) (g : SignedMatrixGate c)
    (y : ℂ) (τ : ℍ) :
    (packet 42 (nodeCoeff c y)).eval (j τ)=actualProduct τ y := by
  rw [← actualMatrix y τ]
  congr 1
  unfold packet matrixSlice
  apply Finset.sum_congr rfl
  intro k hk
  unfold nodeCoeff
  rw [integerRowExact c g k (by have := Finset.mem_range.mp hk; omega)]

end
end Integration.Paper9SignedIntegerMatrixWeld
