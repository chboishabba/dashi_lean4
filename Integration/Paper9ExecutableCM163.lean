import Integration.Paper9FiniteResidualCheck

/-! SOURCE-WRITTEN, UNCOMPILED. Candidate construction is untrusted;
only the finite residual predicates are consumed by the proof. The
closed Lean evaluation has NOT run. The local exact replay of the
same equations is not a Lean proof. -/
namespace Integration.Paper9ExecutableCM163
open scoped BigOperators
open Integration.Paper9FiniteResidualCheck
open Integration.Paper9CM163LiteralPacket

def build (D : ℕ) (f : Array ℤ → ℕ → ℤ) : Array ℤ :=
  (List.range (D+1)).foldl (fun a n => a.push (f a n)) #[]

def candidateU (D : ℕ) : Array ℤ :=
  let a := cube4 (D+1)
  let b := square6 (D+1)
  tab D (fun n => (slot a (n+1)-slot b (n+1))/1728)

def candidateJ (D : ℕ) (u : Array ℤ) : Array ℤ :=
  let a := cube4 (D+1)
  build D (fun j n => slot a n -
    ∑ i ∈ Finset.range n, slot u (i+1)*slot j (n-(i+1)))

def candidateL (diag : Bool) (m D : ℕ) (j : Array ℤ) : Array ℤ :=
  let h := tab (41*D) (hAt diag m j)
  build (41*D) (fun l n =>
    (n:ℤ)*slot h n -
      ∑ i ∈ Finset.range n, slot h (i+1)*slot l (n-(i+1)))

def candidateN (D : ℕ) (l : Array ℤ) : Array ℤ :=
  build D (fun a n =>
    if n=0 then 1 else
      (∑ i ∈ Finset.range n, slot l ((i+1)*41)*slot a (n-(i+1)))/(n:ℤ))

def u := candidateU 3322
def j := candidateJ 3322 u
def ld := candidateL true 3322 82 j
def nd := candidateN 82 ld
def ls := candidateL false 1722 42 j
def ns := candidateN 42 ls

-- Independent finite residual checks, not proofs of the producer.
def unitOK : Bool := decide (unitCheck 3322 u j)
def diagOK : Bool := decide (sectorCheck true 3322 82 j ld nd diagonal)
def sliceOK : Bool := decide (sectorCheck false 1722 42 j ls ns slice)

theorem unitDown (h : unitCheck 3322 u j) : unitCheck 1722 u j := by
  -- Compare the two prefix computations against the same ORIGINAL
  -- mathematical coefficients, not by equality of storage lengths.
  obtain ⟨hu,hj⟩ := unitSound _ _ _ h
  constructor
  · intro i
    have hn : i.val≤1722 := by omega
    have hh := hu i.val (by omega)
    rw [cubeMatches 1723 _ (by omega),squareMatches 1723 _ (by omega)]
    simpa [seriesSlot,PowerSeries.coeff_sub] using hh
  · intro i
    have hn : i.val≤1722 := by omega
    have hh := hj i.val (by omega)
    rw [cubeMatches 1723 _ (by omega)]
    simpa [conv,PowerSeries.coeff_mul,seriesSlot] using hh

theorem diagonalOfCheck (hu : unitOK=true) (hd : diagOK=true) :
    diagonalGate :=
  diagonalChecked u j ld nd (of_decide_eq_true hu) (of_decide_eq_true hd)

theorem sliceOfCheck (hu : unitOK=true) (hs : sliceOK=true) :
    sliceGate :=
  sliceChecked u j ls ns (unitDown (of_decide_eq_true hu)) (of_decide_eq_true hs)

-- Intended local Lean entrypoint after elaboration is paid:
-- #eval (unitOK,diagOK,sliceOK)
-- Do not assert native_decide/kernel acceptance from the external replay.

end Integration.Paper9ExecutableCM163
