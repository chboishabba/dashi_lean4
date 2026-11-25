import Integration.Paper9ActualCMRoot

/-! SOURCE-WRITTEN, UNCOMPILED.
Finite coefficient checker of the ORIGINAL residual premises. Candidate
generation is deliberately outside the soundness proof: every accepted
integer coefficient must satisfy the signed convolution equations.
No hash, floating phase, new analytic function or native_decide premise.
-/
namespace Integration.Paper9FiniteResidualCheck
open Polynomial
open scoped BigOperators
open Integration.Paper9OriginalEisensteinCoeff
open Integration.Paper9EisensteinIntegerBinding
open Integration.Paper9IntegerSectorWeld
open Integration.Paper9ConcreteSectorConsumer
open Integration.Paper9CM163LiteralPacket

def slot (a : Array ℤ) (n : ℕ) : ℤ := a[n]?.getD 0
def tab (D : ℕ) (f : ℕ → ℤ) : Array ℤ :=
  Array.ofFn (fun i : Fin (D+1) => f i.val)

theorem slotTab (D : ℕ) (f : ℕ → ℤ) (n : ℕ) (hn : n≤D) :
    slot (tab D f) n=f n := by
  simp [slot,tab,show n<D+1 by omega]

def conv (a b : Array ℤ) (n : ℕ) : ℤ :=
  ∑ ij ∈ Finset.Nat.antidiagonal n, slot a ij.1*slot b ij.2

def mulPrefix (D : ℕ) (a b : Array ℤ) : Array ℤ := tab D (conv a b)

def series (a : Array ℤ) : PowerSeries ℤ := PowerSeries.mk (slot a)

theorem seriesSlot (a : Array ℤ) (n : ℕ) :
    (series a).coeff n=slot a n := by simp [series]

def seriesMatches (D : ℕ) (a : Array ℤ) (A : PowerSeries ℤ) : Prop :=
  ∀ n≤D, slot a n=A.coeff n

def polyMatches (D : ℕ) (a : Array ℤ) (A : Polynomial ℤ) : Prop :=
  ∀ n≤D, slot a n=A.coeff n

theorem convSeries (D : ℕ) (a b : Array ℤ) (A B : PowerSeries ℤ)
    (ha : seriesMatches D a A) (hb : seriesMatches D b B) :
    seriesMatches D (mulPrefix D a b) (A*B) := by
  intro n hn
  rw [mulPrefix,slotTab _ _ _ hn,conv,PowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro ij hij
  have he := Finset.Nat.mem_antidiagonal.mp hij
  rw [ha ij.1 (by omega),hb ij.2 (by omega)]

theorem convPoly (D : ℕ) (a b : Array ℤ) (A B : Polynomial ℤ)
    (ha : polyMatches D a A) (hb : polyMatches D b B) :
    ∀ n≤D, conv a b n=(A*B).coeff n := by
  intro n hn
  rw [conv,Polynomial.coeff_mul]
  apply Finset.sum_congr rfl
  intro ij hij
  have he := Finset.Nat.mem_antidiagonal.mp hij
  rw [ha ij.1 (by omega),hb ij.2 (by omega)]

def e4Array (D : ℕ) := tab D e4Z
def e6Array (D : ℕ) := tab D e6Z
def cube4 (D : ℕ) := mulPrefix D (mulPrefix D (e4Array D) (e4Array D)) (e4Array D)
def square6 (D : ℕ) := mulPrefix D (e6Array D) (e6Array D)

theorem e4Matches (D : ℕ) : seriesMatches D (e4Array D) e4PSZ := by
  intro n hn
  rw [e4Array,slotTab _ _ _ hn]
  simp [e4PSZ]

theorem e6Matches (D : ℕ) : seriesMatches D (e6Array D) e6PSZ := by
  intro n hn
  rw [e6Array,slotTab _ _ _ hn]
  simp [e6PSZ]

theorem cubeMatches (D : ℕ) : seriesMatches D (cube4 D) (e4PSZ^3) := by
  simpa [cube4,pow_succ] using convSeries D _ _ _ _
    (convSeries D _ _ _ _ (e4Matches D) (e4Matches D)) (e4Matches D)

theorem squareMatches (D : ℕ) : seriesMatches D (square6 D) (e6PSZ^2) := by
  simpa [square6,pow_two] using convSeries D _ _ _ _ (e6Matches D) (e6Matches D)

-- Finite predicates with explicit decidable integer equality. The
-- candidate generator may use division, but the checker never does.
def unitCheck (D : ℕ) (u j : Array ℤ) : Prop :=
  let a := cube4 (D+1)
  let b := square6 (D+1)
  (∀ i : Fin (D+1), 1728*slot u i.val=slot a (i.val+1)-slot b (i.val+1)) ∧
  (∀ i : Fin (D+1), conv u j i.val=slot a i.val)

instance (D : ℕ) (u j : Array ℤ) : Decidable (unitCheck D u j) := by
  unfold unitCheck
  infer_instance

theorem unitSound (D : ℕ) (u j : Array ℤ) (h : unitCheck D u j) :
    (∀ n≤D, 1728*(series u).coeff n=(e4PSZ^3-e6PSZ^2).coeff (n+1)) ∧
    (∀ n≤D, (series u*series j).coeff n=(e4PSZ^3).coeff n) := by
  constructor
  · intro n hn
    have he := h.1 ⟨n,by omega⟩
    rw [cubeMatches (D+1) _ (by omega),squareMatches (D+1) _ (by omega)] at he
    simpa [seriesSlot,PowerSeries.coeff_sub] using he
  · intro n hn
    have he := h.2 ⟨n,by omega⟩
    rw [cubeMatches (D+1) _ (by omega)] at he
    simpa [conv,PowerSeries.coeff_mul,seriesSlot] using he

-- Exact bounded coefficient semantics for the existing polynomial
-- carrier; outside the prefix the polynomial is zero, not guessed.
def poly (m : ℕ) (a : Array ℤ) : Polynomial ℤ := jPrefixZ m (series a)

theorem polySlot (m : ℕ) (a : Array ℤ) (n : ℕ) :
    (poly m a).coeff n=if n≤m then slot a n else 0 := by
  unfold poly jPrefixZ
  rw [Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow,seriesSlot]
  by_cases hn : n≤m
  · rw [if_pos hn,Finset.sum_eq_single n]
    · simp
    · intro i hi hne
      simp [Ne.symm hne,hne]
    · simp [hn]
  · rw [if_neg hn]
    apply Finset.sum_eq_zero
    intro i hi
    have hi' := Finset.mem_range.mp hi
    simp [show n≠i by omega,show i≠n by omega]

def clipped (m : ℕ) (a : Array ℤ) (n : ℕ) : ℤ :=
  if n≤m then slot a n else 0
def ramified (m : ℕ) (a : Array ℤ) (n : ℕ) : ℤ :=
  if 41 ∣ n then clipped m a (n/41) else 0
def shifted (m : ℕ) (a : Array ℤ) (k n : ℕ) : ℤ :=
  if k≤n then clipped m a (n-k) else 0
def mono (c : ℤ) (k n : ℕ) : ℤ := if n=k then c else 0

theorem ramifiedCoeff (m : ℕ) (a : Array ℤ) (n : ℕ) :
    ((poly m a).comp qZ).coeff n=ramified m a n := by
  rw [qZ,← Polynomial.expand_eq_comp_X_pow,Polynomial.coeff_expand (by decide : 0<41)]
  simp [ramified,clipped,polySlot]

theorem shiftedCoeff (m : ℕ) (a : Array ℤ) (k n : ℕ) :
    (Polynomial.X^k*poly m a).coeff n=shifted m a k n := by
  rw [Polynomial.coeff_X_pow_mul']
  simp [shifted,clipped,polySlot]

def hAt (diag : Bool) (m : ℕ) (a : Array ℤ) (n : ℕ) : ℤ :=
  if diag then ramified m a n-shifted m a 40 n
  else clipped m a n-mono (-640320^3) 1 n
def gAt (diag : Bool) (m : ℕ) (a : Array ℤ) (n : ℕ) : ℤ :=
  if diag then shifted m a 40 n-ramified m a n
  else ramified m a n-mono (-640320^3) 41 n

def HZ (diag : Bool) (A : Polynomial ℤ) : Polynomial ℤ :=
  if diag then diagHZ A else sliceHZ A
def GZ (diag : Bool) (A : Polynomial ℤ) : Polynomial ℤ :=
  if diag then diagGZ A else sliceGZ A

theorem hAtCoeff (diag : Bool) (m : ℕ) (a : Array ℤ) (n : ℕ) :
    (HZ diag (poly m a)).coeff n=hAt diag m a n := by
  cases diag <;>
    simp [HZ,hAt,diagHZ,sliceHZ,clipped,mono,polySlot,ramifiedCoeff,
      shiftedCoeff,Polynomial.coeff_C_mul_X_pow,pow_one]

theorem gAtCoeff (diag : Bool) (m : ℕ) (a : Array ℤ) (n : ℕ) :
    (GZ diag (poly m a)).coeff n=gAt diag m a n := by
  cases diag <;>
    simp [GZ,gAt,diagGZ,sliceGZ,clipped,mono,polySlot,ramifiedCoeff,
      shiftedCoeff,Polynomial.coeff_C_mul_X_pow]

-- Horner on the existing normalized columns, truncated after each
-- multiplication. No construction of degree m*d polynomial powers.
def columnArray (D : ℕ) (a c : Array ℤ) : ℕ → Array ℤ
  | 0 => tab D (mono (slot c 0) 0)
  | k+1 =>
      let prev := columnArray D a c k
      tab D (fun n => conv a prev n+mono (slot c (k+1)) (k+1) n)

theorem columnSucc (A : Polynomial ℤ) (c : Array ℤ) (k : ℕ) :
    columnZ A (k+1) c=A*columnZ A k c+
      Polynomial.C (slot c (k+1))*Polynomial.X^(k+1) := by
  unfold columnZ
  rw [Finset.sum_range_succ,Finset.mul_sum]
  simp only [Nat.sub_self,pow_zero,mul_one,slot]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have hi' := Finset.mem_range.mp hi
  rw [show k+1-i=(k-i)+1 by omega,pow_succ]
  ring

theorem columnMatches (D : ℕ) (a c : Array ℤ) (A : Polynomial ℤ)
    (ha : polyMatches D a A) (k : ℕ) :
    polyMatches D (columnArray D a c k) (columnZ A k c) := by
  induction k with
  | zero =>
    intro n hn
    rw [columnArray,slotTab _ _ _ hn]
    simp [columnZ,mono,slot,Polynomial.coeff_C]
  | succ k ih =>
    intro n hn
    rw [columnArray,slotTab _ _ _ hn,columnSucc,Polynomial.coeff_add,
      ← convPoly D a _ A _ ha ih n hn,Polynomial.coeff_C_mul_X_pow]
    simp [mono,eq_comm]

-- Denominator-cleared recurrence is the only acceptance predicate.
def sectorCheck (diag : Bool) (m D : ℕ) (j L N c : Array ℤ) : Prop :=
  let h := tab (41*D) (hAt diag m j)
  let g := tab D (gAt diag m j)
  let v := tab D (fun n => slot L (n*41))
  let a := tab D (clipped m j)
  let col := columnArray D a c D
  slot h 0=1 ∧ slot L 0=0 ∧ slot N 0=1 ∧
  (∀ i : Fin (41*D+1), (i.val:ℤ)*slot h i.val=conv h L i.val) ∧
  (∀ i : Fin (D+1), (i.val:ℤ)*slot N i.val=conv N v i.val) ∧
  (∀ i : Fin (D+1), conv g N i.val=slot col i.val)

instance (diag : Bool) (m D : ℕ) (j L N c : Array ℤ) :
    Decidable (sectorCheck diag m D j L N c) := by
  unfold sectorCheck
  infer_instance

theorem eulerZCoeff (A : Polynomial ℤ) (n : ℕ) :
    (eulerZ A).coeff n=(n:ℤ)*A.coeff n := by
  cases n with
  | zero => simp [eulerZ]
  | succ n =>
    rw [eulerZ,Polynomial.coeff_X_mul,Polynomial.coeff_derivative]
    push_cast
    ring

theorem sectorSound (diag : Bool) (m D : ℕ) (j L N c : Array ℤ)
    (h : sectorCheck diag m D j L N c) :
    let A := poly m j
    let H := HZ diag A
    let G := GZ diag A
    let P := poly (41*D) L
    let Q := poly D N
    H.coeff 0=1 ∧ P.coeff 0=0 ∧ Q.coeff 0=1 ∧
    Polynomial.X^(41*D+1) ∣ eulerZ H-H*P ∧
    Polynomial.X^(D+1) ∣ eulerZ Q-Q*Polynomial.contract 41 P ∧
    Polynomial.X^(D+1) ∣ G*Q-columnZ A D c := by
  dsimp
  let H := HZ diag (poly m j)
  let G := GZ diag (poly m j)
  let P := poly (41*D) L
  let Q := poly D N
  have hh : polyMatches (41*D) (tab (41*D) (hAt diag m j)) H := by
    intro n hn
    rw [slotTab _ _ _ hn,hAtCoeff]
  have hg : polyMatches D (tab D (gAt diag m j)) G := by
    intro n hn
    rw [slotTab _ _ _ hn,gAtCoeff]
  have hp : polyMatches (41*D) L P := by
    intro n hn
    simp [P,polySlot,hn]
  have hq : polyMatches D N Q := by
    intro n hn
    simp [Q,polySlot,hn]
  have hv : polyMatches D (tab D (fun n => slot L (n*41)))
      (Polynomial.contract 41 P) := by
    intro n hn
    rw [slotTab _ _ _ hn,Polynomial.coeff_contract (by decide : 41≠0)]
    exact hp _ (by omega)
  have ha : polyMatches D (tab D (clipped m j)) (poly m j) := by
    intro n hn
    simp [slotTab _ _ _ hn,clipped,polySlot]
  have hc := columnMatches D _ c _ ha D
  obtain ⟨h0,l0,n0,hl,hn,hcol⟩ := h
  refine ⟨(hh 0 (by omega)).symm.trans h0,
    (hp 0 (by omega)).symm.trans l0,(hq 0 (by omega)).symm.trans n0,?_,?_,?_⟩
  · apply Polynomial.X_pow_dvd_iff.mpr
    intro n hlt
    have hi : n≤41*D := by omega
    have he := hl ⟨n,hlt⟩
    rw [hh n hi,convPoly _ _ _ H P hh hp n hi] at he
    simpa [Polynomial.coeff_sub,eulerZCoeff,sub_eq_zero] using he
  · apply Polynomial.X_pow_dvd_iff.mpr
    intro n hlt
    have hi : n≤D := by omega
    have he := hn ⟨n,hlt⟩
    rw [hq n hi,convPoly _ _ _ Q _ hq hv n hi] at he
    simpa [Polynomial.coeff_sub,eulerZCoeff,sub_eq_zero] using he
  · apply Polynomial.X_pow_dvd_iff.mpr
    intro n hlt
    have hi : n≤D := by omega
    have he := hcol ⟨n,hlt⟩
    rw [convPoly _ _ _ G Q hg hq n hi,hc n hi] at he
    simpa [Polynomial.coeff_sub,sub_eq_zero] using he

theorem diagonalChecked (u j L N : Array ℤ)
    (hu : unitCheck 3322 u j)
    (hs : sectorCheck true 3322 82 j L N diagonal) : diagonalGate := by
  obtain ⟨hu',hj⟩ := unitSound _ _ _ hu
  obtain ⟨hH,hL,hN,hl,hn,hc⟩ := sectorSound _ _ _ _ _ _ _ hs
  exact diagonalFromInteger (series u) (series j) (poly 3362 L) (poly 82 N)
    hu' hj hH hL hN hl hn hc

theorem sliceChecked (u j L N : Array ℤ)
    (hu : unitCheck 1722 u j)
    (hs : sectorCheck false 1722 42 j L N slice) : sliceGate := by
  obtain ⟨hu',hj⟩ := unitSound _ _ _ hu
  obtain ⟨hH,hL,hN,hl,hn,hc⟩ := sectorSound _ _ _ _ _ _ _ hs
  exact sliceFromInteger (series u) (series j) (poly 1722 L) (poly 42 N)
    hu' hj hH hL hN hl hn hc

end Integration.Paper9FiniteResidualCheck
