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
      16*((-1:ℚ)^k/((2*k+1:ℕ):ℚ)/(5:ℚ)^(2*k+1))-
      4*((-1:ℚ)^k/((2*k+1:ℕ):ℚ)/(239:ℚ)^(2*k+1)) := by
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


end Integration.Paper9LiteralCross
