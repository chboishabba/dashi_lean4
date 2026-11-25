import Integration.Paper9EisensteinIntegerBinding

/-! SOURCE-WRITTEN, UNCOMPILED.
Direct finite integer residual consumer of the original diagonal and slice
gates. No additional Hecke or analytic carrier; no receipt/hash premise.
The executable integer-array certificate is still required. -/
namespace Integration.Paper9ConcreteSectorConsumer
open Polynomial
open scoped BigOperators
open Integration.Paper9EisensteinIntegerBinding
open Integration.Paper9DiscriminantUnitReflection
open Integration.Paper9HeckeProductAssembly
open Integration.Paper9CyclotomicPacketReflection
open Integration.Paper9IntegerSectorWeld
open Integration.Paper9CM163LiteralPacket

noncomputable section

def jPrefixZ (m : ℕ) (j : PowerSeries ℤ) : Polynomial ℤ :=
  ∑ i ∈ Finset.range (m+1), Polynomial.C (j.coeff i)*Polynomial.X^i

theorem prefixCast (m : ℕ) (u j : PowerSeries ℤ)
    (hu : ∀ n≤m, 1728*u.coeff n=(e4PSZ^3-e6PSZ^2).coeff (n+1))
    (hj : ∀ n≤m, (u*j).coeff n=(e4PSZ^3).coeff n) :
    castPoly (jPrefixZ m j)=jPoly m := by
  unfold jPrefixZ castPoly jPoly
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X]
  rw [jIntegerPrefix m u j hu hj i (by simpa using hi)]
  rfl

def qZ : Polynomial ℤ := Polynomial.X^41
def diagHZ (A : Polynomial ℤ) : Polynomial ℤ :=
  A.comp qZ-Polynomial.X^40*A
def sliceHZ (A : Polynomial ℤ) : Polynomial ℤ :=
  A-Polynomial.C (-640320^3)*Polynomial.X
def diagGZ (A : Polynomial ℤ) : Polynomial ℤ :=
  Polynomial.X^40*A-A.comp qZ
def sliceGZ (A : Polynomial ℤ) : Polynomial ℤ :=
  A.comp qZ-Polynomial.C (-640320^3)*Polynomial.X^41
def columnZ (A : Polynomial ℤ) (d : ℕ) (c : Array ℤ) : Polynomial ℤ :=
  ∑ k ∈ Finset.range (d+1), Polynomial.C (c[k]?.getD 0)*Polynomial.X^k*A^(d-k)

theorem diagHCast (A : Polynomial ℤ) (m : ℕ) (h : castPoly A=jPoly m) :
    castPoly (diagHZ A)=diagH m := by
  simp [diagHZ, diagH, castPoly, qZ, qPoly, Polynomial.map_comp, ← h]

theorem sliceHCast (A : Polynomial ℤ) (m : ℕ) (h : castPoly A=jPoly m) :
    castPoly (sliceHZ A)=sliceH m (-640320^3) := by
  simp [sliceHZ, sliceH, castPoly, ← h]

theorem diagGCast (A : Polynomial ℤ) (m : ℕ) (h : castPoly A=jPoly m) :
    castPoly (diagGZ A)=diagInfinityQ m := by
  simp [diagGZ, diagInfinityQ, castPoly, qZ, qPoly, Polynomial.map_comp, ← h]

theorem sliceGCast (A : Polynomial ℤ) (m : ℕ) (h : castPoly A=jPoly m) :
    castPoly (sliceGZ A)=sliceInfinityQ m (-640320^3) := by
  simp [sliceGZ, sliceInfinityQ, castPoly, qZ, qPoly, Polynomial.map_comp, ← h]

theorem columnCast (A : Polynomial ℤ) (m d : ℕ) (c : Array ℤ)
    (h : castPoly A=jPoly m) :
    castPoly (columnZ A d c)=columnQ m d (fun k => (c[k]?.getD 0 : ℂ)) := by
  unfold columnZ columnQ castPoly
  simp only [map_sum, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow,
    Polynomial.map_X, ← h, castPoly, Int.castRingHom_apply]

-- Compose the existing norm and integer column consumers, keeping the
-- exact residual order and zero modes of H,L,N.
theorem sectorFromResiduals (D : ℕ) (H G C L N : Polynomial ℤ)
    (hH : H.coeff 0=1) (hL : L.coeff 0=0) (hN : N.coeff 0=1)
    (hlog : Polynomial.X^(41*D+1) ∣ eulerZ H-H*L)
    (hnorm : Polynomial.X^(D+1) ∣ eulerZ N-N*Polynomial.contract 41 L)
    (hcol : Polynomial.X^(D+1) ∣ G*N-C) :
    ∀ n≤D, (castPoly G*Polynomial.contract 41 (cyclicNorm (castPoly H))-
        castPoly C).coeff n=0 := by
  intro n hn
  have hnormC := integerNormCast H L N D hH hL hN hlog hnorm
  have hm := mulCoeffTransport D (castPoly G) _ _ hnormC n hn
  have hc := integerColumnResidual D G N C hcol n hn
  rw [Polynomial.coeff_sub, hm]
  simpa only [Polynomial.coeff_sub] using hc

-- The literal arrays are consumed in their original descending order.
-- These residual premises are exactly the executable finite obligations;
-- no cyclotomic complex-number evaluation is required of the checker.
theorem diagonalFromInteger (u j : PowerSeries ℤ) (L N : Polynomial ℤ)
    (hu : ∀ n≤3322, 1728*u.coeff n=(e4PSZ^3-e6PSZ^2).coeff (n+1))
    (hj : ∀ n≤3322, (u*j).coeff n=(e4PSZ^3).coeff n)
    (hH : (diagHZ (jPrefixZ 3322 j)).coeff 0=1)
    (hL : L.coeff 0=0) (hN : N.coeff 0=1)
    (hlog : Polynomial.X^3363 ∣ eulerZ (diagHZ (jPrefixZ 3322 j))-
      diagHZ (jPrefixZ 3322 j)*L)
    (hnorm : Polynomial.X^83 ∣ eulerZ N-N*Polynomial.contract 41 L)
    (hcol : Polynomial.X^83 ∣ diagGZ (jPrefixZ 3322 j)*N-
      columnZ (jPrefixZ 3322 j) 82 diagonal) :
    diagonalGate := by
  have hp := prefixCast 3322 u j hu hj
  have hs := sectorFromResiduals 82 _ _ _ L N hH hL hN hlog hnorm hcol
  rw [diagHCast _ _ hp, diagGCast _ _ hp, columnCast _ _ _ _ hp] at hs
  exact hs

theorem sliceFromInteger (u j : PowerSeries ℤ) (L N : Polynomial ℤ)
    (hu : ∀ n≤1722, 1728*u.coeff n=(e4PSZ^3-e6PSZ^2).coeff (n+1))
    (hj : ∀ n≤1722, (u*j).coeff n=(e4PSZ^3).coeff n)
    (hH : (sliceHZ (jPrefixZ 1722 j)).coeff 0=1)
    (hL : L.coeff 0=0) (hN : N.coeff 0=1)
    (hlog : Polynomial.X^1723 ∣ eulerZ (sliceHZ (jPrefixZ 1722 j))-
      sliceHZ (jPrefixZ 1722 j)*L)
    (hnorm : Polynomial.X^43 ∣ eulerZ N-N*Polynomial.contract 41 L)
    (hcol : Polynomial.X^43 ∣ sliceGZ (jPrefixZ 1722 j)*N-
      columnZ (jPrefixZ 1722 j) 42 slice) :
    sliceGate := by
  have hp := prefixCast 1722 u j hu hj
  have hs := sectorFromResiduals 42 _ _ _ L N hH hL hN hlog hnorm hcol
  rw [sliceHCast _ _ hp, sliceGCast _ _ hp, columnCast _ _ _ _ hp] at hs
  exact hs

end
end Integration.Paper9ConcreteSectorConsumer
