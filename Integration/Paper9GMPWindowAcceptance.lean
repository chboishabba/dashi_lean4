import Integration.Paper9NativeFiniteAcceptance

/-! SOURCE-WRITTEN, UNCOMPILED. Direct production endpoint on the
existing literal Chudnovsky prefix and arbitrary positive GMP scale.
No new analytic premise, no claimed cross-kernel proof import. -/
namespace Integration.Paper9GMPWindowAcceptance

open Filter
open scoped Topology
open Integration.Paper9LiteralFactorialPrefix
open Integration.Paper9LiteralWindow
open Integration.Paper9LiteralCross
open Integration.Paper9NativeFiniteAcceptance

-- GMP's leaf and binary join, on the original prefix record.
def empty : RawPrefix := ⟨1,1,0⟩
def atom (n : ℕ) : RawPrefix :=
  ⟨leafP n,leafQ n,leafP n*weight n⟩
def join (l r : RawPrefix) : RawPrefix :=
  ⟨l.p*r.p,l.q*r.q,l.t*(r.q:ℤ)+l.p*r.t⟩

theorem joinAssoc (a b c : RawPrefix) :
    join (join a b) c = join a (join b c) := by
  cases a; cases b; cases c
  simp only [join,RawPrefix.mk.injEq,Nat.cast_mul]
  constructor
  · ring
  constructor <;> ring

theorem joinEmptyLeft (a : RawPrefix) : join empty a = a := by
  cases a
  simp [join,empty]

theorem joinEmptyRight (a : RawPrefix) : join a empty = a := by
  cases a
  simp [join,empty]

def segment (a : ℕ) : ℕ → RawPrefix
  | 0 => empty
  | n+1 => join (segment a n) (atom (a+n))

theorem segmentAppend (a m n : ℕ) :
    segment a (m+n) = join (segment a m) (segment (a+m) n) := by
  induction n with
  | zero => simp [segment,joinEmptyRight]
  | succ n ih =>
    rw [show m+(n+1)=m+n+1 by omega,segment,ih,segment,joinAssoc]
    rw [Nat.add_assoc]

theorem segmentOne (a : ℕ) : segment a 1 = atom a := by
  simp [segment,joinEmptyLeft]

theorem segmentPrefix (n : ℕ) : segment 0 n = prefix n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [segment,ih,Nat.zero_add,prefix,join,atom]
    congr 1 <;> ring

-- Reduced GMP joins need not preserve raw bytes. They preserve the
-- pair of rational observations (P/Q,T/Q), on positive denominators.
def pVal (a : RawPrefix) : ℚ := (a.p:ℚ)/(a.q:ℚ)
def tVal (a : RawPrefix) : ℚ := (a.t:ℚ)/(a.q:ℚ)
def Equivalent (a b : RawPrefix) : Prop :=
  pVal a=pVal b ∧ tVal a=tVal b

theorem joinValues (a b : RawPrefix) (ha : 0<a.q) (hb : 0<b.q) :
    pVal (join a b)=pVal a*pVal b ∧
    tVal (join a b)=tVal a+pVal a*tVal b := by
  have ha' : (a.q:ℚ)≠0 := by exact_mod_cast ha.ne'
  have hb' : (b.q:ℚ)≠0 := by exact_mod_cast hb.ne'
  constructor <;> simp only [join,pVal,tVal,Int.cast_mul,Int.cast_add,
    Int.cast_natCast,Nat.cast_mul] <;> field_simp [ha',hb'] <;> ring

theorem joinCong (a b a' b' : RawPrefix)
    (ha : 0<a.q) (hb : 0<b.q) (ha' : 0<a'.q) (hb' : 0<b'.q)
    (ea : Equivalent a a') (eb : Equivalent b b') :
    Equivalent (join a b) (join a' b') := by
  obtain ⟨hp,ht⟩ := joinValues a b ha hb
  obtain ⟨hp',ht'⟩ := joinValues a' b' ha' hb'
  exact ⟨hp.trans ((congrArg₂ (· * ·) ea.1 eb.1).trans hp'.symm),
    ht.trans ((congrArg₂ (· + ·) ea.2 (congrArg₂ (· * ·) ea.1 eb.2)).trans ht'.symm)⟩

-- Actual cross-GCD reduction used by the GMP split: l.p/g and r.q/g.
-- The exact quotient equations are the integer division witnesses.
theorem crossCancel (l r : RawPrefix) (g q' : ℕ) (p' : ℤ)
    (hg : 0<g) (hq : 0<q') (hl : 0<l.q)
    (hp : l.p=(g:ℤ)*p') (hr : r.q=g*q') :
    Equivalent (join l r)
      (join ⟨p',l.q,l.t⟩ ⟨r.p,q',r.t⟩) := by
  have hg' : (g:ℚ)≠0 := by exact_mod_cast hg.ne'
  have hq' : (q':ℚ)≠0 := by exact_mod_cast hq.ne'
  have hl' : (l.q:ℚ)≠0 := by exact_mod_cast hl.ne'
  constructor <;> simp only [join,pVal,tVal,hp,hr,Int.cast_mul,Int.cast_add,
    Int.cast_natCast,Nat.cast_mul] <;> field_simp [hg',hq',hl'] <;> ring

-- Analytic endpoint is composed directly from the existing eight finite
-- decision proofs, not from a Boolean asserted by a foreign program.
theorem actualPrefixLimit :
    Tendsto (fun N => (Integration.Paper9LiteralFactorialPrefix.sum N:ℂ))
      atTop (𝓝 ((426880*Real.sqrt 10005/Real.pi:ℝ):ℂ)) :=
  Integration.Paper9DiskGerm.literalPrefixFromFiniteChecks
    unitChecked diagonalChecked shiftChecked sliceChecked jetChecked
    piChecked sqrtChecked expChecked

theorem gmpWindow (n r scale : ℕ) (hn : 1≤n) (hs : 0<scale)
    (hl : r^2≤10005*scale^2) (hu : 10005*scale^2<(r+1)^2) :
    (low n r scale:ℝ)≤Real.pi ∧ Real.pi≤(high n r scale:ℝ) :=
  actualPiInside actualPrefixLimit n r scale hn hs hl hu.le

-- One-floor certificate: lower endpoint >= x and upper endpoint < x+1.
-- Both endpoints are exact rationals and arbitrary positive scales.
theorem floorFromWindow (n r scale d : ℕ) (x : ℤ)
    (hn : 1≤n) (hs : 0<scale)
    (hl : r^2≤10005*scale^2) (hu : 10005*scale^2<(r+1)^2)
    (hL : (x:ℚ)≤(10:ℚ)^d*low n r scale)
    (hU : (10:ℚ)^d*high n r scale<(x:ℚ)+1) :
    ⌊(10:ℝ)^d*Real.pi⌋=x := by
  obtain ⟨a,b⟩ := gmpWindow n r scale hn hs hl hu
  have hL' : (x:ℝ)≤(10:ℝ)^d*(low n r scale:ℝ) := by exact_mod_cast hL
  have hU' : (10:ℝ)^d*(high n r scale:ℝ)<(x:ℝ)+1 := by exact_mod_cast hU
  exact Int.floor_eq_iff.mpr
    ⟨hL'.trans (mul_le_mul_of_nonneg_left a (by positivity)),
      (mul_le_mul_of_nonneg_left b (by positivity)).trans_lt hU'⟩

-- Exact integer residuals of the raw original window. A strict upper
-- test is required; an upper endpoint equal to x+1 is not admitted.
theorem floorFromRaw (n r scale d : ℕ) (x : ℤ)
    (hn : 1≤n) (hs : 0<scale)
    (hl : r^2≤10005*scale^2) (hu : 10005*scale^2<(r+1)^2)
    (hL : x*((rawWindow n r scale).1.2:ℤ)≤
      (10:ℤ)^d*(rawWindow n r scale).1.1)
    (hU : (10:ℤ)^d*(rawWindow n r scale).2.1<
      (x+1)*((rawWindow n r scale).2.2:ℤ)) :
    ⌊(10:ℝ)^d*Real.pi⌋=x := by
  obtain ⟨vl,vu⟩ := rawWindowValue n r scale hn hs
  obtain ⟨dl,du⟩ := rawWindowDenPositive n r scale hn hs
  apply floorFromWindow n r scale d x hn hs hl hu
  · rw [← vl]
    unfold value
    rw [← mul_div_assoc]
    apply (le_div_iff₀ (by exact_mod_cast dl)).2
    exact_mod_cast hL
  · rw [← vu]
    unfold value
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ (by exact_mod_cast du)).2
    exact_mod_cast hU

#print axioms actualPrefixLimit
#print axioms floorFromRaw
#print axioms crossCancel
end Integration.Paper9GMPWindowAcceptance
