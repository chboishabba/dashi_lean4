import Integration.Paper9NativeFiniteAcceptance

/-! Source-written, uncompiled. Proof-side correspondence for the original
GMP binary split (signed P,T; positive Q), cross-GCD cancellation and
one-division decimal admission. No new analytic identity. -/
namespace Integration.Paper9GmpCertificate
open Integration.Paper9LiteralFactorialPrefix
open Integration.Paper9LiteralWindow
open Integration.Paper9NativeFiniteAcceptance

def empty : RawPrefix := ⟨1,1,0⟩
def leafTriple (n : ℕ) : RawPrefix :=
  ⟨leafP n, leafQ n, leafP n * weight n⟩

def join (l r : RawPrefix) : RawPrefix :=
  ⟨l.p*r.p,l.q*r.q,l.t*(r.q:ℤ)+l.p*r.t⟩

theorem joinAssoc (a b c : RawPrefix) :
    join (join a b) c = join a (join b c) := by
  cases a; cases b; cases c
  simp only [join, RawPrefix.mk.injEq, Nat.cast_mul]
  constructor
  · ring
  constructor <;> ring

theorem emptyLeft (a : RawPrefix) : join empty a = a := by
  cases a
  simp [join,empty]

theorem emptyRight (a : RawPrefix) : join a empty = a := by
  cases a
  simp [join,empty]

theorem prefixSucc (n : ℕ) : prefix (n+1)=join (prefix n) (leafTriple n) := by
  simp only [prefix,join,leafTriple]
  congr 1
  ring

def fold (xs : List ℕ) : RawPrefix :=
  xs.foldl (fun a n => join a (leafTriple n)) empty

theorem foldFrom (a : RawPrefix) (xs : List ℕ) :
    xs.foldl (fun a n => join a (leafTriple n)) a = join a (fold xs) := by
  induction xs generalizing a with
  | nil => simp [fold,emptyRight]
  | cons n xs ih =>
    change xs.foldl (fun u i => join u (leafTriple i)) (join a (leafTriple n)) =
      join a (xs.foldl (fun u i => join u (leafTriple i)) (join empty (leafTriple n)))
    rw [ih (join a (leafTriple n)),ih (join empty (leafTriple n)),emptyLeft,joinAssoc]

theorem foldAppend (xs ys : List ℕ) :
    fold (xs++ys) = join (fold xs) (fold ys) := by
  unfold fold
  rw [List.foldl_append]
  exact foldFrom _ _

theorem foldRange (n : ℕ) : fold (List.range n)=prefix n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ,foldAppend,ih,prefixSucc]
    simp [fold,emptyLeft]

inductive Tree where
  | nil
  | single (i : ℕ)
  | branch (l r : Tree)

def leaves : Tree → List ℕ
  | .nil => []
  | .single i => [i]
  | .branch l r => leaves l ++ leaves r

def plain : Tree → RawPrefix
  | .nil => empty
  | .single i => leafTriple i
  | .branch l r => join (plain l) (plain r)

theorem plainFold (t : Tree) : plain t = fold (leaves t) := by
  induction t with
  | nil => rfl
  | single i => simp [plain,leaves,fold,emptyLeft]
  | branch l r hl hr => simp only [plain,leaves,foldAppend,hl,hr]

theorem plainPrefix (t : Tree) (n : ℕ) (h : leaves t=List.range n) :
    plain t=prefix n := by rw [plainFold,h,foldRange]

def productValue (u : RawPrefix) : ℚ := (u.p:ℚ)/(u.q:ℚ)
def sumValue (u : RawPrefix) : ℚ := (u.t:ℚ)/(u.q:ℚ)

def Equivalent (a b : RawPrefix) : Prop :=
  0<a.q ∧ 0<b.q ∧ productValue a=productValue b ∧ sumValue a=sumValue b

theorem joinQ (a b : RawPrefix) (ha : 0<a.q) (hb : 0<b.q) :
    0<(join a b).q := Nat.mul_pos ha hb

theorem joinValues (a b : RawPrefix) (ha : 0<a.q) (hb : 0<b.q) :
    productValue (join a b)=productValue a*productValue b ∧
    sumValue (join a b)=sumValue a+productValue a*sumValue b := by
  have ha' : (a.q:ℚ)≠0 := by exact_mod_cast ha.ne'
  have hb' : (b.q:ℚ)≠0 := by exact_mod_cast hb.ne'
  constructor <;>
    simp only [join,productValue,sumValue,Int.cast_mul,Int.cast_add,
      Int.cast_natCast,Nat.cast_mul] <;> field_simp [ha',hb'] <;> ring

theorem joinCong {a b c d : RawPrefix}
    (h : Equivalent a b) (k : Equivalent c d) :
    Equivalent (join a c) (join b d) := by
  obtain ⟨ha,hb,hp,ht⟩ := h
  obtain ⟨hc,hd,kp,kt⟩ := k
  obtain ⟨h1,h2⟩ := joinValues a c ha hc
  obtain ⟨h3,h4⟩ := joinValues b d hb hd
  exact ⟨joinQ a c ha hc,joinQ b d hb hd,
    by rw [h1,h3,hp,kp],by rw [h2,h4,hp,ht,kt]⟩

-- Actual C++ cross-GCD step: replace l.p by lp, r.q by rq,
-- with l.p=g*lp and r.q=g*rq. All three original joined coordinates
-- have exactly the SAME factor g, including signed T.
def reducedJoin (l r : RawPrefix) (lp : ℤ) (rq : ℕ) : RawPrefix :=
  join ⟨lp,l.q,l.t⟩ ⟨r.p,rq,r.t⟩

theorem reducedCoordinates (l r : RawPrefix) (g rq : ℕ) (lp : ℤ)
    (hp : l.p=(g:ℤ)*lp) (hq : r.q=g*rq) :
    (join l r).p=(g:ℤ)*(reducedJoin l r lp rq).p ∧
    (join l r).q=g*(reducedJoin l r lp rq).q ∧
    (join l r).t=(g:ℤ)*(reducedJoin l r lp rq).t := by
  simp only [join,reducedJoin,hp,hq,Nat.cast_mul]
  constructor
  · ring
  constructor <;> ring

theorem reducedSound (l r : RawPrefix) (g rq : ℕ) (lp : ℤ)
    (hg : 0<g) (hrq : 0<rq) (hl : 0<l.q)
    (hp : l.p=(g:ℤ)*lp) (hq : r.q=g*rq) :
    Equivalent (reducedJoin l r lp rq) (join l r) := by
  have hred : 0<(reducedJoin l r lp rq).q := Nat.mul_pos hl hrq
  have hplain : 0<(join l r).q := Nat.mul_pos hl (by rw [hq]; exact Nat.mul_pos hg hrq)
  obtain ⟨ep,eq,et⟩ := reducedCoordinates l r g rq lp hp hq
  have hg' : (g:ℚ)≠0 := by exact_mod_cast hg.ne'
  have hq' : ((reducedJoin l r lp rq).q:ℚ)≠0 := by exact_mod_cast hred.ne'
  refine ⟨hred,hplain,?_,?_⟩
  · unfold productValue
    rw [ep,eq]
    push_cast
    field_simp [hg',hq'] <;> ring
  · unfold sumValue
    rw [et,eq]
    push_cast
    field_simp [hg',hq'] <;> ring

theorem equivalentTrans {a b c : RawPrefix} (h : Equivalent a b) (k : Equivalent b c) :
    Equivalent a c := ⟨h.1,k.2.1,h.2.2.1.trans k.2.2.1,h.2.2.2.trans k.2.2.2⟩

-- A proof-relevant trace of the original split. Plain joins cover the
-- threshold branch; reduced joins require the literal exact divisions.
inductive Evaluates : Tree → RawPrefix → Prop where
  | nil : Evaluates .nil empty
  | single (i : ℕ) : Evaluates (.single i) (leafTriple i)
  | join {l r : Tree} {a b : RawPrefix} :
      Evaluates l a → Evaluates r b → Evaluates (.branch l r) (join a b)
  | reduce {l r : Tree} {a b : RawPrefix} (g rq : ℕ) (lp : ℤ) :
      Evaluates l a → Evaluates r b → 0<g → 0<rq →
      a.p=(g:ℤ)*lp → b.q=g*rq →
      Evaluates (.branch l r) (reducedJoin a b lp rq)

theorem evaluatesSound {t : Tree} {a : RawPrefix} (h : Evaluates t a) :
    Equivalent a (plain t) := by
  induction h with
  | nil => exact ⟨by decide,by decide,rfl,rfl⟩
  | single i => exact ⟨leafQ_pos i,leafQ_pos i,rfl,rfl⟩
  | join _ _ ha hb => exact joinCong ha hb
  | reduce g rq lp _ _ hg hrq hp hq ha hb =>
    exact equivalentTrans (reducedSound _ _ g rq lp hg hrq ha.1 hp hq) (joinCong ha hb)

theorem prefixSound {t : Tree} {a : RawPrefix} (n : ℕ)
    (h : Evaluates t a) (hl : leaves t=List.range n) :
    Equivalent a (prefix n) := by
  rw [← plainPrefix t n hl]
  exact evaluatesSound h

-- Same original analytic endpoint, at arbitrary GMP indices/scale, not
-- the smaller Machin-stage cutoff. The eight finite decisions are the
-- existing proof owners, not a new external analytic premise.
theorem piWindow (n r scale : ℕ) (hn : 1≤n) (hs : 0<scale)
    (hl : r^2≤10005*scale^2) (hu : 10005*scale^2≤(r+1)^2) :
    (low n r scale:ℝ)≤Real.pi ∧ Real.pi≤(high n r scale:ℝ) :=
  actualPiInside
    (Integration.Paper9DiskGerm.literalPrefixFromFiniteChecks
      unitChecked diagonalChecked shiftChecked sliceChecked jetChecked
      piChecked sqrtChecked expChecked) n r scale hn hs hl hu

-- One lower floor and a strict upper boundary. The GMP upper equality
-- case is deliberately rejected. This states the floor semantics without
-- relying on a decimal-output hash.
theorem decimalAdmission (n r scale digits : ℕ) (x : ℤ)
    (hn : 1≤n) (hs : 0<scale)
    (hl : r^2≤10005*scale^2) (hu : 10005*scale^2≤(r+1)^2)
    (hlo : (x:ℚ)≤low n r scale*10^digits)
    (hhi : high n r scale*10^digits<(x:ℚ)+1) :
    (x:ℝ)≤Real.pi*10^digits ∧ Real.pi*10^digits<(x:ℝ)+1 := by
  obtain ⟨hL,hU⟩ := piWindow n r scale hn hs hl hu
  have h1 : (x:ℝ)≤(low n r scale:ℝ)*10^digits := by exact_mod_cast hlo
  have h2 : (high n r scale:ℝ)*10^digits<(x:ℝ)+1 := by exact_mod_cast hhi
  exact ⟨h1.trans (mul_le_mul_of_nonneg_right hL (by positivity)),
    (mul_le_mul_of_nonneg_right hU (by positivity)).trans_lt h2⟩

def gmpLow (a b : RawPrefix) (r scale : ℕ) : ℚ :=
  (426880*r:ℚ)/(scale:ℚ)/max (sumValue a) (sumValue b)
def gmpHigh (a b : RawPrefix) (r scale : ℕ) : ℚ :=
  (426880*(r+1):ℚ)/(scale:ℚ)/min (sumValue a) (sumValue b)

theorem gmpAdmission {ta tb : Tree} {a b : RawPrefix}
    (n r scale digits : ℕ) (x : ℤ)
    (ha : Evaluates ta a) (hb : Evaluates tb b)
    (hla : leaves ta=List.range n) (hlb : leaves tb=List.range (n+1))
    (hn : 1≤n) (hs : 0<scale)
    (hl : r^2≤10005*scale^2) (hu : 10005*scale^2≤(r+1)^2)
    (hlo : (x:ℚ)≤gmpLow a b r scale*10^digits)
    (hhi : gmpHigh a b r scale*10^digits<(x:ℚ)+1) :
    (x:ℝ)≤Real.pi*10^digits ∧ Real.pi*10^digits<(x:ℝ)+1 := by
  have hA := (prefixSound n ha hla).2.2.2
  have hB := (prefixSound (n+1) hb hlb).2.2.2
  unfold gmpLow at hlo
  unfold gmpHigh at hhi
  rw [hA,hB] at hlo hhi
  exact decimalAdmission n r scale digits x hn hs hl hu hlo hhi

#print axioms gmpAdmission
end Integration.Paper9GmpCertificate
