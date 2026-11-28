import Mathlib
import Welds.PNPSameRunReadFootprintExact

namespace PNPMultiCutCrossing

-- An epoch may do arbitrary internal work and reuse on its own side.
-- All cross-cut information is an incoming finite control message.
-- A side's local memory is reconstructed from its input and history.
-- Halt is an explicit terminal event, not an uncharged timing channel.
def trace {A M : Type*} (step : Bool → A → List M → Sum Bool M)
    (x y : A) : Nat → Bool → List M → List (Sum Bool M)
  | 0, _, _ => []
  | k+1, p, hist =>
    let e := step p (if p then x else y) hist
    e :: (match e with
          | .inl _ => []
          | .inr m => trace step x y k (!p) (m::hist))

theorem mix {A M : Type*} (step : Bool → A → List M → Sum Bool M)
    (x y : A) (k : Nat) (p : Bool) (hist : List M)
    (h : trace step x x k p hist = trace step y y k p hist) :
    trace step x y k p hist = trace step x x k p hist := by
  induction k generalizing p hist with
  | zero => rfl
  | succ k ih =>
    have h' := h
    simp only [trace,ite_self] at h'
    have hh := List.cons.inj h'
    cases hx : step p x hist with
    | inl b =>
      have hy : step p y hist = Sum.inl b := hh.1.symm.trans hx
      cases p <;> simp [trace,hx,hy]
    | inr m =>
      have hy : step p y hist = Sum.inr m := hh.1.symm.trans hx
      have ht : trace step x x k (!p) (m::hist) =
          trace step y y k (!p) (m::hist) := by
        simpa [hx,hy] using hh.2
      have hm := ih (!p) (m::hist) ht
      cases p <;> simp [trace,hx,hy,hm]

theorem diagonal_injective {A M : Type*}
    (step : Bool → A → List M → Sum Bool M)
    (observe : List (Sum Bool M) → Bool) (k : Nat) (p : Bool)
    (sound : ∀ x y, observe (trace step x y k p []) = true ↔ x=y) :
    Function.Injective (fun x : A => trace step x x k p []) := by
  intro x y h
  apply (sound x y).mp
  rw [mix step x y k p [] h]
  exact (sound x x).mpr rfl

-- Fixed-length option padding is injective for actual short words.
-- Counts halt markers and termination/length, not just the payload.
def shortCode {M : Type*} (K : Nat) (xs : List M) : Fin K → Option M :=
  fun i => xs[i.val]?

theorem shortCode_injective {M : Type*} (K : Nat) (xs ys : List M)
    (hx : xs.length≤K) (hy : ys.length≤K)
    (h : shortCode K xs = shortCode K ys) : xs=ys := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i<K
  · exact congrFun h ⟨i,hi⟩
  · have hx' : xs.length≤i := by omega
    have hy' : ys.length≤i := by omega
    simp [List.getElem?_eq_none hx',List.getElem?_eq_none hy']

-- Simultaneous counting: if all inputs had a short transcript on some
-- cut, choose one such cut and inject into cut × padded word.
-- Thus one actual input has long transcripts across ALL cuts.
theorem all_cuts_long {A C M : Type*} [Fintype A] [Fintype C] [Fintype M]
    (words : C → A → List M) (inj : ∀ c, Function.Injective (words c))
    (K : Nat)
    (large : Fintype.card C * (Fintype.card M+1)^K < Fintype.card A) :
    ∃ x, ∀ c, K < (words c x).length := by
  classical
  by_contra h
  push_neg at h
  let chooseCut : A → C := fun x => Classical.choose (h x)
  have short : ∀ x, (words (chooseCut x) x).length≤K :=
    fun x => Classical.choose_spec (h x)
  let code : A → C × (Fin K → Option M) :=
    fun x => (chooseCut x,shortCode K (words (chooseCut x) x))
  have hc : Function.Injective code := by
    intro x y eq
    have h1 : chooseCut x = chooseCut y := congrArg Prod.fst eq
    have h2 : shortCode K (words (chooseCut x) x) =
        shortCode K (words (chooseCut y) y) := congrArg Prod.snd eq
    apply inj (chooseCut x)
    apply shortCode_injective K _ _ (short x)
    · simpa [h1] using short y
    · simpa [h1] using h2
  have hb := Fintype.card_le_of_injective code hc
  have hb' : Fintype.card A ≤ Fintype.card C * (Fintype.card M+1)^K := by
    simpa using hb
  exact (not_le_of_gt large) hb'

-- Distinct physical cuts: one unit head movement crosses at most one.
-- Each transcript has at most one terminal event in addition to
-- crossing messages. The sum inequality is the actual locality premise.
theorem same_run_lower {A C M : Type*} [Fintype A] [Fintype C] [Fintype M]
    (words : C → A → List M) (inj : ∀ c, Function.Injective (words c))
    (cross : C → A → Nat) (time : A → Nat)
    (charged : ∀ x, (∑ c, cross c x)≤time x)
    (lengthBound : ∀ c x, (words c x).length≤cross c x+1)
    (K : Nat)
    (large : Fintype.card C * (Fintype.card M+1)^K < Fintype.card A) :
    ∃ x, Fintype.card C*K≤time x := by
  obtain ⟨x,hx⟩ := all_cuts_long words inj K large
  refine ⟨x,?_⟩
  calc
    Fintype.card C*K = ∑ _c : C, K := by simp
    _ ≤ ∑ c, cross c x := by
      apply Finset.sum_le_sum
      intro c _
      have ha := hx c
      have hb := lengthBound c x
      omega
    _ ≤ time x := charged x

-- For g=Theta(n) physical tape separators, fixed alphabet M, choose
-- K=floor((n-log2(2g))/log2(|M|+1)). This yields a quadratic worst
-- case in the SINGLE-HEAD local tape model. Arbitrary DAG/RAM or
-- binary-exponent stack macros do not satisfy the unit-cut charge.
end PNPMultiCutCrossing


namespace PNPMultiCutCrossing

-- Actual distinct-cut charge: a unit head step yields either no
-- crossing or ONE cut coordinate. This is not a graph edge count
-- inferred from input/output dependence.
def crossingEvent (p q : ℤ) : Option ℤ :=
  if q=p+1 then some p else if p=q+1 then some q else none

theorem stay_event (p : ℤ) : crossingEvent p p = none := by
  simp [crossingEvent]; omega

theorem right_event (p : ℤ) : crossingEvent p (p+1) = some p := by
  simp [crossingEvent]

theorem left_event (p : ℤ) : crossingEvent p (p-1) = some (p-1) := by
  have h : p-1≠p+1 := by omega
  have h' : p=p-1+1 := by omega
  simp [crossingEvent,h,h']

def cutCount (c : ℤ) : List (Option ℤ) → Nat
  | [] => 0
  | e::es => (if e=some c then 1 else 0)+cutCount c es

theorem one_event (C : Finset ℤ) (e : Option ℤ) :
    (∑ c ∈ C, if e=some c then (1:Nat) else 0) ≤ 1 := by
  classical
  cases e with
  | none => simp
  | some a =>
    simp only [Option.some.injEq]
    rw [Finset.sum_ite_eq']
    split <;> omega

theorem disjoint_cut_charge (C : Finset ℤ) (events : List (Option ℤ)) :
    (∑ c ∈ C, cutCount c events) ≤ events.length := by
  induction events with
  | nil => simp [cutCount]
  | cons e es ih =>
    simp only [cutCount,List.length_cons,Finset.sum_add_distrib]
    have h := one_event C e
    omega

-- Composition with the earlier simultaneous transcript bound requires
-- the actual physical trace to supply these events (one per step) and
-- its local crossing protocol to reconstruct the observed transcript.
end PNPMultiCutCrossing
