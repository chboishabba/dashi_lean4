import Integration.Paper9UniversalMonicSlice
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic

/-! Source-written, kernel pending. The parameter polynomial lives in the
coefficient ring of the original ramified polynomial. Evaluation is a ring
homomorphism, not an identification of the F43 field with integer nodes.
The existing arbitrary-parameter analytic consumer remains the endpoint. -/
namespace Integration.Paper9SignedUniversalMatrix
open Polynomial Complex UpperHalfPlane
open scoped BigOperators
open Integration.Paper9HeckeProductAssembly
open Integration.Paper9CyclotomicPacketReflection
open Integration.Paper9UniversalMonicSlice
open Integration.Paper9Hecke41ChartGeometry
noncomputable section
abbrev YPoly := Polynomial ℂ
abbrev QPoly := Polynomial YPoly

def liftQ (p : Polynomial ℂ) : QPoly := p.map (Polynomial.C : ℂ →+* YPoly)
def atY (y : ℂ) : QPoly →+* Polynomial ℂ :=
  Polynomial.mapRingHom (Polynomial.evalRingHom y)

theorem atLift (y : ℂ) (p : Polynomial ℂ) : atY y (liftQ p)=p := by
  ext n
  simp [atY,liftQ,Polynomial.coeff_map]

def signedH : QPoly := liftQ (jPoly 1722)-C (X : YPoly)*X
def signedInfinity : QPoly := liftQ ((jPoly 1722).comp qPoly)-C (X : YPoly)*X^41

def signedScale (a : ℂ) : QPoly →+* QPoly :=
  Polynomial.compRingHom (C (C a : YPoly)*X)

theorem atScale (y a : ℂ) (H : QPoly) :
    atY y (signedScale a H)=scale a (atY y H) := by
  change (H.comp (C (C a : YPoly)*X)).map _ =
    ((H.map _).comp (C a*X))
  rw [Polynomial.map_comp]
  simp

def signedNorm : QPoly := ∏ a : Fin 41, signedScale (phase a) signedH

theorem atH (y : ℂ) : atY y signedH=sliceH 1722 y := by
  simp [signedH,sliceH,atLift,atY]

theorem atInfinity (y : ℂ) : atY y signedInfinity=sliceInfinityQ 1722 y := by
  simp [signedInfinity,sliceInfinityQ,atLift,atY]

theorem atNorm (y : ℂ) : atY y signedNorm=cyclicNorm (sliceH 1722 y) := by
  unfold signedNorm cyclicNorm
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro a ha
  rw [atScale,atH]

-- Coefficient extraction is exactly the existing contraction at 41.
def signedRow (n : ℕ) : YPoly :=
  (signedInfinity * Polynomial.contract 41 signedNorm).coeff n

theorem atContract (y : ℂ) (H : QPoly) :
    atY y (Polynomial.contract 41 H)=Polynomial.contract 41 (atY y H) := by
  ext n
  simp [atY,Polynomial.coeff_map,Polynomial.coeff_contract (by decide : 41≠0)]

theorem signedRowRead (y : ℂ) (n : ℕ) :
    (signedRow n).eval y=(target y).coeff n := by
  have h := congrArg (fun A : Polynomial ℂ => A.coeff n)
    (show atY y (signedInfinity * Polynomial.contract 41 signedNorm)=target y by
      rw [map_mul,atInfinity,atContract,atNorm,target])
  simpa [signedRow,atY,Polynomial.coeff_map] using h

-- Deterministic triangular recursion, not 43 independent choices.
def rows : ℕ → YPoly
  | n => signedRow n - ∑ k ∈ (Finset.range n).attach,
      rows k.val * C (pivot (jPoly 1722) 42 n k.val)
termination_by n
decreasing_by
  exact Finset.mem_range.mp k.property

theorem rowsRead (y : ℂ) (n : ℕ) (hn : n≤42) :
    (rows n).eval y=sliceC y n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have h := sliceResidual y n hn
    rw [Polynomial.coeff_sub,columnQCoeff _ _ _ _ hn,Finset.sum_range_succ,
      pivotOne _ (jPolyZero 1722),mul_one] at h
    rw [rows,Polynomial.eval_sub,Polynomial.eval_sum,signedRowRead]
    have hs : (∑ k ∈ (Finset.range n).attach,
        (rows k.val * C (pivot (jPoly 1722) 42 n k.val)).eval y)=
      ∑ k ∈ Finset.range n, sliceC y k*pivot (jPoly 1722) 42 n k := by
      rw [← Finset.sum_attach (s := Finset.range n)]
      apply Finset.sum_congr rfl
      intro k hk
      have hkn := Finset.mem_range.mp k.property
      simp [ih k.val hkn (by omega)]
    rw [hs]
    linear_combination h

def matrixSlice (y : ℂ) : Polynomial ℂ := packet 42 (fun n => (rows n).eval y)

theorem matrixSliceEq (y : ℂ) : matrixSlice y=universalSlice y := by
  unfold matrixSlice universalSlice packet
  apply Finset.sum_congr rfl
  intro k hk
  rw [rowsRead y k (by have := Finset.mem_range.mp hk; omega)]

theorem actualMatrix (y : ℂ) (τ : ℍ) :
    (matrixSlice y).eval (Integration.MoonshineEisensteinAgdaTarget.jTarget τ)=actualProduct τ y := by
  rw [matrixSliceEq,universalSliceEval]

-- Signed parameter readback: coefficients of even and odd powers are
-- retained independently. At nonzero nodes both reads are required.
def evenRead (p : YPoly) (y : ℂ) := (p.eval y+p.eval (-y))/2
def oddRead (p : YPoly) (y : ℂ) := (p.eval y-p.eval (-y))/2

theorem signedReconstruct (p : YPoly) (y : ℂ) :
    evenRead p y+oddRead p y=p.eval y ∧
    evenRead p y-oddRead p y=p.eval (-y) := by
  constructor <;> unfold evenRead oddRead <;> ring

-- The leading monic coefficient is identical; only 42 signed nodes
-- are needed for the difference, once its degree <=41 is established.
theorem signedNodeUnique (p q : YPoly) (hdeg : (p-q).natDegree<42)
    (h : ∀ i : Fin 21, p.eval (i.val+1 : ℂ)=q.eval (i.val+1 : ℂ) ∧
      p.eval (-(i.val+1 : ℂ))=q.eval (-(i.val+1 : ℂ))) : p=q := by
  let node : Fin 42 → ℂ := fun i =>
    if i.val<21 then (i.val+1 : ℂ) else -((i.val-20 : ℕ) : ℂ)
  have hinj : Function.Injective node := by
    intro i j hij
    apply Fin.ext
    dsimp [node] at hij
    by_cases hi : i.val<21 <;> by_cases hj : j.val<21
    · simp only [hi,hj,if_true] at hij
      have he : (i.val : ℂ)=(j.val : ℂ) := add_right_cancel hij
      exact_mod_cast he
    · simp only [hi,hj,if_true,if_false] at hij
      have he := congrArg Complex.re hij
      simp at he
      have hp : (0:ℝ)<(i.val:ℝ)+1 := by positivity
      have hn : (0:ℝ)≤((j.val-20:ℕ):ℝ) := by positivity
      linarith
    · simp only [hi,hj,if_true,if_false] at hij
      have he := congrArg Complex.re hij
      simp at he
      have hp : (0:ℝ)<(j.val:ℝ)+1 := by positivity
      have hn : (0:ℝ)≤((i.val-20:ℕ):ℝ) := by positivity
      linarith
    · simp only [hi,hj,if_false,neg_inj] at hij
      have he : i.val-20=j.val-20 := by exact_mod_cast hij
      omega
  have hz (i : Fin 42) : (p-q).eval (node i)=0 := by
    rw [Polynomial.eval_sub,sub_eq_zero]
    by_cases hi : i.val<21
    · simpa [node,hi] using (h ⟨i.val,hi⟩).1
    · let k : Fin 21 := ⟨i.val-21,by omega⟩
      have he : i.val-20=k.val+1 := by dsimp [k]; omega
      simpa [node,hi,he,Nat.cast_add] using (h k).2
  exact sub_eq_zero.mp (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
    (p-q) hinj hz (by simpa using hdeg))

-- Existing integer matrix is attached by the actual normalized row
-- equations, not digest equality or a new analytic hypothesis.
theorem integerMatrixConsumer (c : ℂ → ℕ → ℂ)
    (h : ∀ y n, n≤42 → (target y-columnQ 1722 42 (c y)).coeff n=0) :
    ∀ y τ, (packet 42 (c y)).eval (Integration.MoonshineEisensteinAgdaTarget.jTarget τ)=
      (matrixSlice y).eval (Integration.MoonshineEisensteinAgdaTarget.jTarget τ) := by
  intro y τ
  rw [actualMatrix]
  exact (sliceSectorConsumer y (c y) (h y) τ).symm
end
end Integration.Paper9SignedUniversalMatrix
