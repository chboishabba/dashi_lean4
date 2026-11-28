import Integration.Paper9SignedUniversalMatrix
import Integration.Paper9SeparatedCusp
import Mathlib.Tactic

/-! Source-written, kernel pending. The original separated cusp theorem
supplies the infinite j-image; no new separation premise. -/
namespace Integration.Paper9UniversalMatrixSymmetry
open Polynomial Complex UpperHalfPlane
open scoped BigOperators
open Integration.Paper9SignedUniversalMatrix
open Integration.Paper9UniversalMonicSlice
open Integration.Paper9SymmetricTauJet
open Integration.Paper9SeparatedCusp
open Integration.Paper9Hecke41ChartGeometry
open Integration.Paper9HeckeProductAssembly
noncomputable section
local notation "j" => Integration.MoonshineEisensteinAgdaTarget.jTarget

def rowInY (x : ℂ) : Polynomial ℂ :=
  ∑ k ∈ Finset.range 43, C (x^(42-k))*rows k

theorem rowEval (x y : ℂ) : (rowInY x).eval y=(matrixSlice y).eval x := by
  unfold rowInY matrixSlice packet
  simp only [Polynomial.eval_sum,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_pow,Polynomial.eval_X]
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem rowActual (τ : ℍ) : rowInY (j τ)=rootPoly τ := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply Set.infinite_univ.mono
  intro y hy
  rw [Set.mem_setOf_eq,rowEval,actualMatrix,rootEval]

def transposedColumn (n : ℕ) : Polynomial ℂ :=
  packet 42 (fun k => (rows k).coeff n)

theorem transposedRead (x : ℂ) (n : ℕ) :
    (transposedColumn n).eval x=(rowInY x).coeff n := by
  unfold transposedColumn packet rowInY
  simp only [Polynomial.eval_sum,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_pow,Polynomial.eval_X,Polynomial.finset_sum_coeff,
    Polynomial.coeff_C_mul]
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem transposedAbove (n : ℕ) (hn : 42<n) : transposedColumn n=0 := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply separatedImageInfinite.mono
  intro x hx
  obtain ⟨τ,rfl,_⟩ := hx
  rw [Set.mem_setOf_eq,transposedRead,rowActual,Polynomial.eval_zero]
  exact Polynomial.natDegree_le_iff_coeff_eq_zero.mp (rootDegree τ).le n hn

theorem packetCoeff (c : ℕ → ℂ) (k : ℕ) (hk : k≤42) :
    (packet 42 c).coeff (42-k)=c k := by
  unfold packet
  rw [Polynomial.finset_sum_coeff,Finset.sum_eq_single k]
  · simp [Polynomial.coeff_C_mul_X_pow]
  · intro i hi hne
    have hi' := Finset.mem_range.mp hi
    have he : 42-i ≠ 42-k := by omega
    simp [Polynomial.coeff_C_mul_X_pow,he,Ne.symm he]
  · intro h
    exact (h (Finset.mem_range.mpr (by omega))).elim

-- Reverse solve the degree bound from the original analytic root product.
-- This avoids bounding every intermediate cyclotomic coefficient.
theorem rowsDegree (k : ℕ) (hk : k≤42) : (rows k).natDegree≤42 := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  have h := congrArg (fun P : Polynomial ℂ => P.coeff (42-k))
    (transposedAbove n hn)
  simpa [transposedColumn,packetCoeff _ _ hk] using h

theorem transposedTop : transposedColumn 42=1 := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply separatedImageInfinite.mono
  intro x hx
  obtain ⟨τ,rfl,_⟩ := hx
  rw [Set.mem_setOf_eq,transposedRead,rowActual,Polynomial.eval_one,
    ← rootDegree τ]
  exact rootMonic τ

theorem rowLeading (k : ℕ) (hk : k≤42) :
    (rows k).coeff 42=if k=42 then 1 else 0 := by
  have h := congrArg (fun P : Polynomial ℂ => P.coeff (42-k)) transposedTop
  rw [transposedColumn,packetCoeff _ _ hk] at h
  by_cases h' : k=42
  · subst k; simpa using h
  · have hn : 42-k≠0 := by omega
    simpa [h',Polynomial.coeff_one,hn,Ne.symm hn] using h

-- Symmetry of the actual source product already proved by SeparatedCusp.
-- Lift it twice through the infinite image; no chart separation at CM.
theorem rowTranspose (x y : ℂ) : (rowInY x).eval y=(rowInY y).eval x := by
  have h (τ : ℍ) : rowInY (j τ)=matrixSlice (j τ) := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply separatedImageInfinite.mono
    intro v hv
    obtain ⟨σ,rfl,_⟩ := hv
    rw [Set.mem_setOf_eq,rowEval,actualMatrix,actualMatrix]
    exact actualSymmetry σ τ
  have hxy : matrixSlice y=rowInY y := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply separatedImageInfinite.mono
    intro v hv
    obtain ⟨τ,rfl,_⟩ := hv
    rw [Set.mem_setOf_eq,← rowEval,h τ]
  rw [rowEval,hxy]

-- Compare two polynomial rows on 42 signed integer nodes, after
-- paying degree and the actual leading coefficient.
theorem rowFromSigned (k : ℕ) (hk : k≤42) (p : Polynomial ℂ)
    (hp : p.natDegree≤42) (htop : p.coeff 42=(rows k).coeff 42)
    (h : ∀ i : Fin 21,
      p.eval (i.val+1 : ℂ)=(rows k).eval (i.val+1 : ℂ) ∧
      p.eval (-(i.val+1 : ℂ))=(rows k).eval (-(i.val+1 : ℂ))) :
    p=rows k := by
  apply signedNodeUnique p (rows k) _ h
  have hd : (p-rows k).natDegree≤41 := by
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro n hn
    by_cases he : n=42
    · subst n; simp [Polynomial.coeff_sub,htop]
    · have hn' : 42<n := by omega
      rw [Polynomial.coeff_sub,
        Polynomial.natDegree_le_iff_coeff_eq_zero.mp hp n hn',
        Polynomial.natDegree_le_iff_coeff_eq_zero.mp (rowsDegree k hk) n hn',
        sub_zero]
  omega
end
end Integration.Paper9UniversalMatrixSymmetry
