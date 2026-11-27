import Integration.Paper9GmpCertificate

/-! Source-written executable trace checker. It consumes exact division
coordinates, not a trusted GMP Boolean or a hash. The theorem accepts
arbitrary trace sizes, arbitrary digits and the original analytic endpoint.
The replay data is optional for production timing. -/
namespace Integration.Paper9GmpTraceChecker
open Integration.Paper9LiteralFactorialPrefix
open Integration.Paper9GmpCertificate

inductive Trace where
  | empty
  | leaf (i : ℕ)
  | merge (l r : Trace) (g rq : ℕ) (lp : ℤ)
  deriving Repr

def tree : Trace → Tree
  | .empty => .nil
  | .leaf i => .single i
  | .merge l r _ _ _ => .branch (tree l) (tree r)

def checked : Trace → Option RawPrefix
  | .empty => some empty
  | .leaf i => some (leafTriple i)
  | .merge l r g rq lp =>
    match checked l, checked r with
    | some a, some b =>
      if 0<g ∧ 0<rq ∧ a.p=(g:ℤ)*lp ∧ b.q=g*rq
      then some (reducedJoin a b lp rq)
      else none
    | _,_ => none

theorem checkedSound (t : Trace) (a : RawPrefix) (h : checked t=some a) :
    Evaluates (tree t) a := by
  induction t generalizing a with
  | empty =>
    simp [checked] at h
    subst a
    exact Evaluates.nil
  | leaf i =>
    simp [checked] at h
    subst a
    exact Evaluates.single i
  | merge l r g rq lp il ir =>
    cases hl : checked l with
    | none => simp [checked,hl] at h
    | some u =>
      cases hr : checked r with
      | none => simp [checked,hl,hr] at h
      | some v =>
        simp only [checked,hl,hr] at h
        split at h
        next hc =>
          have he := Option.some.inj h
          subst a
          exact Evaluates.reduce g rq lp (il u hl) (ir v hr) hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
        next hc => contradiction

-- The second production prefix is literally a single non-reduced leaf
-- append. Build its exact division coordinates with g=1.
def appendLeaf (t : Trace) (a : RawPrefix) (n : ℕ) : Trace :=
  .merge t (.leaf n) 1 (leafQ n) a.p

theorem appendChecked (t : Trace) (a : RawPrefix) (n : ℕ)
    (h : checked t=some a) : checked (appendLeaf t a n)=some (join a (leafTriple n)) := by
  have hq := leafQ_pos n
  simp [appendLeaf,checked,h,hq,reducedJoin,leafTriple,join]

-- Match the adapter's exact receipt, including the root's strict upper
-- square and the strict upper decimal floor. Avoid any normalized-Rat
-- byte equality: the raw integer products remain the checked objects.
structure Receipt where
  digits : ℕ
  n : ℕ
  r : ℕ
  scale : ℕ
  x : ℤ
  deriving Repr

def Accepts (t : Trace) (a : RawPrefix) (w : Receipt) : Prop :=
  leaves (tree t)=List.range w.n ∧
  1≤w.n ∧ 0<w.scale ∧
  w.r^2≤10005*w.scale^2 ∧ 10005*w.scale^2<(w.r+1)^2 ∧
  (w.x:ℚ)≤gmpLow a (join a (leafTriple w.n)) w.r w.scale*10^w.digits ∧
  gmpHigh a (join a (leafTriple w.n)) w.r w.scale*10^w.digits<(w.x:ℚ)+1

instance (t : Trace) (a : RawPrefix) (w : Receipt) : Decidable (Accepts t a w) := by
  unfold Accepts
  infer_instance

def check (t : Trace) (w : Receipt) : Bool :=
  match checked t with
  | none => false
  | some a => decide (Accepts t a w)

theorem sound (t : Trace) (w : Receipt) (h : check t w=true) :
    (w.x:ℝ)≤Real.pi*10^w.digits ∧ Real.pi*10^w.digits<(w.x:ℝ)+1 := by
  cases ht : checked t with
  | none => simp [check,ht] at h
  | some a =>
    have hc : Accepts t a w := by
      have hd : decide (Accepts t a w)=true := by simpa [check,ht] using h
      exact of_decide_eq_true hd
    obtain ⟨hlist,hn,hs,hl,hu,hlo,hhi⟩ := hc
    have ha := checkedSound t a ht
    have hb := checkedSound (appendLeaf t a w.n) (join a (leafTriple w.n)) (appendChecked t a w.n ht)
    have hlistB : leaves (tree (appendLeaf t a w.n))=List.range (w.n+1) := by
      simp [appendLeaf,tree,leaves,hlist,List.range_succ]
    exact gmpAdmission w.n w.r w.scale w.digits w.x ha hb hlist hlistB hn hs hl hu.le hlo hhi

#print axioms sound
end Integration.Paper9GmpTraceChecker
