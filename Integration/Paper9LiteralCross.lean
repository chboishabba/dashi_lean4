import Integration.Paper9LiteralWindow
import Mathlib.Data.Nat.Sqrt

/-! SOURCE-WRITTEN, UNCOMPILED.
Literal source indices and Machin stages, using the existing alternating
bracket and original period consumer. A universal Lean rational statement
is not a transported Agda proof. -/
namespace Integration.Paper9LiteralCross
open Filter
open scoped Topology BigOperators
open Integration.Paper9LiteralWindow
open Integration.Paper9CMOriginalMachinWindow

def cutoff (k : ℕ) : ℕ := 1+(k+4)/41
def rootScale (k : ℕ) : ℕ := 2^(k+2)
def rootNumerator (k : ℕ) : ℕ := Nat.sqrt (10005*(rootScale k)^2)
def machinStage (k : ℕ) : ℚ := 16*prefixRat 5 k-4*prefixRat 239 k
def radius : ℕ → ℚ
  | 0 => 22/7
  | k+1 => 4/(25:ℚ)^(k+1)

theorem rootWitness (k : ℕ) :
    rootNumerator k^2≤10005*rootScale k^2 ∧
      10005*rootScale k^2<(rootNumerator k+1)^2 := by
  exact ⟨Nat.sqrt_le' _, Nat.lt_succ_sqrt' _⟩

-- Exact uniqueness at the source's strict integer floor boundary.
-- The upper non-strict square inequality alone would not identify a floor.
theorem rootUnique (k r : ℕ) (h1 : r^2≤10005*rootScale k^2)
    (h2 : 10005*rootScale k^2<(r+1)^2) : r=rootNumerator k :=
  Nat.eq_sqrt'.2 ⟨h1,h2⟩

theorem prefixStep (x : ℝ) (n : ℕ) :
    prefix x (n+1)=prefix x n+(-1:ℝ)^n*magnitude x n := by
  unfold prefix
  rw [Finset.sum_range_succ]

-- Either parity is retained: the two neighboring partials enclose the
-- actual arctangent. The first omitted term bounds the signed difference.
theorem atanError (x : ℝ) (hx : 0≤x) (hx1 : x<1) (n : ℕ) :
    |Real.arctan x-prefix x n|≤magnitude x n := by
  have hmag (k : ℕ) : 0≤magnitude x k := by unfold magnitude; positivity
  let j := n/2
  have hn : n=2*j ∨ n=2*j+1 := by dsimp [j]; omega
  obtain ⟨hl,hu⟩ := atanBracket x hx hx1 j
  have hnxt := (atanBracket x hx hx1 (j+1)).1
  rcases hn with h|h
  · rw [h,abs_le]
    have hs := prefixStep x (2*j)
    rw [pow_mul] at hs
    norm_num at hs
    exact ⟨by linarith [hmag (2*j), hmag (2*j+1)],by linarith [hmag (2*j),hmag (2*j+1)]⟩
  · rw [h,abs_le]
    have hs := prefixStep x (2*j+1)
    rw [pow_add,pow_mul] at hs
    norm_num at hs
    rw [show 2*(j+1)=2*j+1+1 by omega] at hnxt
    exact ⟨by linarith [hmag (n/2*2), hmag (2*j), hmag (2*j+1)],by linarith [hmag (2*j),hmag (2*j+1)]⟩

theorem magnitudeFifth (x : ℝ) (hx : 0≤x) (h : x≤1/5) (n : ℕ) :
    magnitude x n≤1/(5:ℝ)*(1/25:ℝ)^n := by
  have hp : x^(2*n+1)≤(1/5:ℝ)^(2*n+1) := by gcongr
  have hn : (1:ℝ)≤((2*n+1:ℕ):ℝ) := by
    exact_mod_cast (show 1≤2*n+1 by omega)
  calc
    magnitude x n≤x^(2*n+1) := by
      unfold magnitude
      exact div_le_self (pow_nonneg hx _) hn
    _ ≤ _ := hp
    _ = _ := by rw [pow_succ,pow_mul]; norm_num <;> ring

theorem machinGeometric (n : ℕ) :
    |Real.pi-(machinStage n:ℝ)|≤4/(25:ℝ)^n := by
  have h5 := abs_le.mp (atanError (1/5) (by norm_num) (by norm_num) n)
  have h239 := abs_le.mp (atanError (1/239) (by norm_num) (by norm_num) n)
  have b5 := magnitudeFifth (1/5) (by norm_num) (by norm_num) n
  have b239 := magnitudeFifth (1/239) (by norm_num) (by norm_num) n
  have hm := Real.four_mul_arctan_inv_5_sub_arctan_inv_239
  change 4*Real.arctan (1/5)-Real.arctan (1/239)=Real.pi/4 at hm
  unfold machinStage
  push_cast
  rw [prefixCast 5 n (by decide),prefixCast 239 n (by decide),abs_le]
  have hpow : (1/25:ℝ)^n=1/(25:ℝ)^n := by rw [div_pow,one_pow]
  rw [hpow] at b5 b239
  exact ⟨by linarith [h5.1,h239.2],by linarith [h5.2,h239.1]⟩

theorem machinZeroRadius : |Real.pi-(machinStage 0:ℝ)|≤(22/7:ℝ) := by
  have h5 := (atanBracket (1/5) (by norm_num) (by norm_num) 1).2
  have h239 := (atanBracket (1/239) (by norm_num) (by norm_num) 1).1
  have hm := Real.four_mul_arctan_inv_5_sub_arctan_inv_239
  change 4*Real.arctan (1/5)-Real.arctan (1/239)=Real.pi/4 at hm
  norm_num [prefix,magnitude,Finset.sum_range_succ] at h5 h239
  have hp : Real.pi≤22/7 := by linarith
  simpa [machinStage,prefixRat,abs_of_nonneg Real.pi_pos.le] using hp

theorem machinRadiusSound (k : ℕ) :
    |Real.pi-(machinStage k:ℝ)|≤(radius k:ℝ) := by
  cases k with
  | zero => simpa [radius] using machinZeroRadius
  | succ n => simpa [radius] using machinGeometric (n+1)

-- No arbitrary root, cutoff, Machin center or radius remains.
theorem crossAt (h : Tendsto
    (fun N => (Integration.Paper9LiteralFactorialPrefix.sum N:ℂ)) atTop
    (𝓝 ((426880*Real.sqrt 10005/Real.pi:ℝ):ℂ))) (k : ℕ) :
    low (cutoff k) (rootNumerator k) (rootScale k)≤machinStage k+radius k ∧
    machinStage k≤high (cutoff k) (rootNumerator k) (rootScale k)+radius k := by
  exact rationalCross h _ _ _ (by unfold cutoff; omega)
    (by unfold rootScale; positivity) (rootWitness k).1 (rootWitness k).2.le
    _ _ (machinRadiusSound k)

-- The four raw positive denominator pairs are source coordinates.
-- Keep these equations explicit until the actual cross-prover witness
-- is checked. No assumption that a normalized Rat has the same bytes.
theorem fractionLeIff (a b : ℤ) (c d : ℕ) (hc : 0<c) (hd : 0<d) :
    ((a:ℚ)/(c:ℚ)≤(b:ℚ)/(d:ℚ)) ↔ a*(d:ℤ)≤b*(c:ℤ) := by
  rw [div_le_div_iff₀ (by exact_mod_cast hc : 0<(c:ℚ))
    (by exact_mod_cast hd : 0<(d:ℚ))]
  constructor <;> intro h <;> exact_mod_cast h

theorem crossCoordinates
    (l u m e : ℚ) (hl : l≤m+e) (hu : m≤u+e)
    (ln un mn en : ℤ) (ld ud md ed : ℕ)
    (hld : 0<ld) (hud : 0<ud) (hmd : 0<md) (hed : 0<ed)
    (L : l=(ln:ℚ)/(ld:ℚ)) (U : u=(un:ℚ)/(ud:ℚ))
    (M : m=(mn:ℚ)/(md:ℚ)) (E : e=(en:ℚ)/(ed:ℚ)) :
    ln*(md:ℤ)*(ed:ℤ)≤(mn*(ed:ℤ)+en*(md:ℤ))*(ld:ℤ) ∧
    mn*(ud:ℤ)*(ed:ℤ)≤(un*(ed:ℤ)+en*(ud:ℤ))*(md:ℤ) := by
  rw [L,M,E] at hl
  rw [M,U,E] at hu
  have hld' : (ld:ℚ)≠0 := by exact_mod_cast hld.ne'
  have hud' : (ud:ℚ)≠0 := by exact_mod_cast hud.ne'
  have hmd' : (md:ℚ)≠0 := by exact_mod_cast hmd.ne'
  have hed' : (ed:ℚ)≠0 := by exact_mod_cast hed.ne'
  have h1 : (mn:ℚ)/(md:ℚ)+(en:ℚ)/(ed:ℚ)=
      ((mn:ℚ)*(ed:ℚ)+(en:ℚ)*(md:ℚ))/((md:ℚ)*(ed:ℚ)) := by
    field_simp [hmd',hed']; ring
  have h2 : (un:ℚ)/(ud:ℚ)+(en:ℚ)/(ed:ℚ)=
      ((un:ℚ)*(ed:ℚ)+(en:ℚ)*(ud:ℚ))/((ud:ℚ)*(ed:ℚ)) := by
    field_simp [hud',hed']; ring
  rw [h1,div_le_div_iff₀ (by positivity) (by positivity)] at hl
  rw [h2,div_le_div_iff₀ (by positivity) (by positivity)] at hu
  constructor
  · exact_mod_cast (show (ln:ℚ)*(md:ℚ)*(ed:ℚ)≤
      ((mn:ℚ)*(ed:ℚ)+(en:ℚ)*(md:ℚ))*(ld:ℚ) by simpa [mul_assoc] using hl)
  · exact_mod_cast (show (mn:ℚ)*(ud:ℚ)*(ed:ℚ)≤
      ((un:ℚ)*(ed:ℚ)+(en:ℚ)*(ud:ℚ))*(md:ℚ) by simpa [mul_assoc] using hu)

-- Raw source fields, not a replacement arithmetic or real carrier.
-- Agda's qMachinTerm performs the same unreduced products and sums.
abbrev Raw := ℤ × ℕ
def value (p : Raw) : ℚ := (p.1:ℚ)/(p.2:ℚ)
def addRaw (p q : Raw) : Raw :=
  (p.1*(q.2:ℤ)+q.1*(p.2:ℤ),p.2*q.2)

theorem addRawValue (p q : Raw) (hp : 0<p.2) (hq : 0<q.2) :
    value (addRaw p q)=value p+value q := by
  have hp' : (p.2:ℚ)≠0 := by exact_mod_cast hp.ne'
  have hq' : (q.2:ℚ)≠0 := by exact_mod_cast hq.ne'
  unfold value addRaw
  push_cast
  field_simp [hp',hq'] <;> ring

def omittedDen (d k : ℕ) : ℕ := (2*k+1)*d^(2*k+1)
def rawTerm (k : ℕ) : Raw :=
  let a := omittedDen 5 k
  let b := omittedDen 239 k
  ((-1:ℤ)^k*(16*(b:ℤ)-4*(a:ℤ)),a*b)

def rawStage : ℕ → Raw
  | 0 => (0,1)
  | k+1 => addRaw (rawStage k) (rawTerm k)

def rawRadius : ℕ → Raw
  | 0 => (22,7)
  | k+1 => (4,25^(k+1))

theorem rawTermDenPositive (k : ℕ) : 0<(rawTerm k).2 := by
  simp only [rawTerm,omittedDen]
  positivity

theorem rawStageDenPositive (k : ℕ) : 0<(rawStage k).2 := by
  induction k with
  | zero => decide
  | succ k ih => exact Nat.mul_pos ih (rawTermDenPositive k)

theorem rawTermValue (k : ℕ) :
    value (rawTerm k) =
      16*((-1:ℚ)^k/(((2*k+1:ℕ):ℚ)*(5:ℚ)^(2*k+1)))-
      4*((-1:ℚ)^k/(((2*k+1:ℕ):ℚ)*(239:ℚ)^(2*k+1))) := by
  unfold value rawTerm omittedDen
  push_cast
  field_simp <;> ring

theorem rawStageValue (k : ℕ) : value (rawStage k)=machinStage k := by
  induction k with
  | zero => norm_num [rawStage,value,machinStage,prefixRat]
  | succ k ih =>
    change value (addRaw (rawStage k) (rawTerm k))=machinStage (k+1)
    rw [addRawValue _ _ (rawStageDenPositive k) (rawTermDenPositive k),
      ih,rawTermValue]
    unfold machinStage prefixRat
    rw [Finset.sum_range_succ,Finset.sum_range_succ]
    ring

theorem rawRadiusValue (k : ℕ) : value (rawRadius k)=radius k := by
  cases k <;> simp [value,rawRadius,radius]


local notation "Pfx" => Integration.Paper9LiteralFactorialPrefix.prefix
local notation "S" => Integration.Paper9LiteralFactorialPrefix.sum

-- The original positiveView uses T and Q with B=1. No reduction
-- by gcd is done in these exported coordinates.
def rawCorner (n r s : ℕ) : Raw :=
  (Int.ofNat (426880*r*(Pfx n).q),s*(Pfx n).t.toNat)

theorem prefixTPositive (n : ℕ) (hn : 1≤n) : 0<(Pfx n).t := by
  have h : 0<S n := (loPositive n hn).trans_le (min_le_left _ _)
  have hq : 0<((Pfx n).q:ℚ) := by
    exact_mod_cast Integration.Paper9LiteralFactorialPrefix.prefixQ_pos n
  change 0<((Pfx n).t:ℚ)/((Pfx n).q:ℚ) at h
  have ht := (lt_div_iff₀ hq).1 h
  simp only [zero_mul] at ht
  exact_mod_cast ht

theorem rawCornerPositive (n r s : ℕ) (hn : 1≤n) (hs : 0<s) :
    0<(rawCorner n r s).2 := by
  have ht := prefixTPositive n hn
  have hcast := Int.toNat_of_nonneg ht.le
  change 0<s*(Pfx n).t.toNat
  exact Nat.mul_pos hs (by omega)

theorem rawCornerValue (n r s : ℕ) (hn : 1≤n) (hs : 0<s) :
    value (rawCorner n r s)=(426880*r:ℚ)/(s:ℚ)/S n := by
  have ht := prefixTPositive n hn
  have hcast : (((Pfx n).t.toNat:ℕ):ℚ)=((Pfx n).t:ℚ) := by
    exact_mod_cast Int.toNat_of_nonneg ht.le
  have htn : ((Pfx n).t:ℚ)≠0 := by exact_mod_cast ht.ne'
  have hqn : ((Pfx n).q:ℚ)≠0 := by
    exact_mod_cast (Integration.Paper9LiteralFactorialPrefix.prefixQ_pos n).ne'
  have hsn : (s:ℚ)≠0 := by exact_mod_cast hs.ne'
  unfold rawCorner value Integration.Paper9LiteralFactorialPrefix.sum
  push_cast
  rw [hcast]
  field_simp [htn,hqn,hsn] <;> ring

theorem rawSort (n : ℕ) :
    S n≤S (n+1) ↔
      (Pfx n).t*((Pfx (n+1)).q:ℤ)≤(Pfx (n+1)).t*((Pfx n).q:ℤ) :=
  fractionLeIff _ _ _ _
    (Integration.Paper9LiteralFactorialPrefix.prefixQ_pos n)
    (Integration.Paper9LiteralFactorialPrefix.prefixQ_pos (n+1))

def rawWindow (n r s : ℕ) : Raw × Raw :=
  if S n≤S (n+1) then
    (rawCorner (n+1) r s,rawCorner n (r+1) s)
  else
    (rawCorner n r s,rawCorner (n+1) (r+1) s)

theorem rawWindowValue (n r s : ℕ) (hn : 1≤n) (hs : 0<s) :
    value (rawWindow n r s).1=low n r s ∧
    value (rawWindow n r s).2=high n r s := by
  have hn' : 1≤n+1 := by omega
  unfold rawWindow low high lo hi
  split
  next h =>
    simp only [min_eq_left h,max_eq_right h]
    exact ⟨rawCornerValue _ _ _ hn' hs,rawCornerValue _ _ _ hn hs⟩
  next h =>
    have h' := le_of_not_ge h
    simp only [min_eq_right h',max_eq_left h']
    exact ⟨rawCornerValue _ _ _ hn hs,rawCornerValue _ _ _ hn' hs⟩

theorem rawWindowDenPositive (n r s : ℕ) (hn : 1≤n) (hs : 0<s) :
    0<(rawWindow n r s).1.2 ∧ 0<(rawWindow n r s).2.2 := by
  have hn' : 1≤n+1 := by omega
  unfold rawWindow
  split <;> exact ⟨rawCornerPositive _ _ _ (by omega) hs,
    rawCornerPositive _ _ _ (by omega) hs⟩

-- All-index literal INTEGER cross on the source-shaped raw fields.
-- This still needs actual cross-kernel proof transportation.
def RawCross (k : ℕ) : Prop :=
    let w := rawWindow (cutoff k) (rootNumerator k) (rootScale k)
    let l := w.1
    let u := w.2
    let m := rawStage k
    let e := rawRadius k
    l.1*(m.2:ℤ)*(e.2:ℤ)≤(m.1*(e.2:ℤ)+e.1*(m.2:ℤ))*(l.2:ℤ) ∧
    m.1*(u.2:ℤ)*(e.2:ℤ)≤(u.1*(e.2:ℤ)+e.1*(u.2:ℤ))*(m.2:ℤ)

theorem rawCrossAt (h : Tendsto
    (fun N => (S N:ℂ)) atTop (𝓝 ((426880*Real.sqrt 10005/Real.pi:ℝ):ℂ)))
    (k : ℕ) : RawCross k := by
  unfold RawCross
  dsimp
  have hn : 1≤cutoff k := by unfold cutoff; omega
  have hs : 0<rootScale k := by unfold rootScale; positivity
  obtain ⟨hl,hu⟩ := crossAt h k
  obtain ⟨hL,hU⟩ := rawWindowValue _ _ _ hn hs
  obtain ⟨hdL,hdU⟩ := rawWindowDenPositive _ _ _ hn hs
  have he : 0<(rawRadius k).2 := by cases k <;> simp [rawRadius] <;> positivity
  exact crossCoordinates _ _ _ _ hl hu _ _ _ _ _ _ _ _
    hdL hdU (rawStageDenPositive k) he hL.symm hU.symm
    (rawStageValue k).symm (rawRadiusValue k).symm


-- A4/A5/A7 + F5 in one explicit source theorem. Still no native
-- decider/kernel receipt and no proof transport into Agda.
theorem rawCrossFromFiniteChecks
    (hu : Integration.Paper9ExecutableCM163.unitOK=true)
    (hd : Integration.Paper9ExecutableCM163.diagOK=true)
    (hz : Integration.Paper9CMShiftCheck.shiftOK=true)
    (hs : Integration.Paper9ExecutableCM163.sliceOK=true)
    (hc : Integration.Paper9ScalarCross.jetOK=true)
    (hp : Integration.Paper9CMOriginalMachinWindow.piRoundOK)
    (hq : Integration.Paper9CMOriginalMachinWindow.sqrtRoundOK)
    (hw : Integration.Paper9CMNormalizedCuspWindow.expWindowOK) :
    ∀ k, RawCross k :=
  rawCrossAt (Integration.Paper9DiskGerm.literalPrefixFromFiniteChecks
    hu hd hz hs hc hp hq hw)

end Integration.Paper9LiteralCross
