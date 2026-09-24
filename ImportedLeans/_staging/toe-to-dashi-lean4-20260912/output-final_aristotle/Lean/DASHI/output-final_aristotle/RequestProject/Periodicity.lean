import RequestProject.Defects

/-!
# The periodicity search

A `subclass of` cycle in Wikidata is a *periodic point* of the class hierarchy:
an item that the hierarchy walks back to after a fixed number of steps.  This
file develops the search for such points and for their periods, first for an
arbitrary finitely branching step function and then for the `subclass of` graph
of a knowledge base.

The abstract layer (`Wikidata.Periodicity`):

* `ReachIn step n x y` — `y` is reached from `x` in **exactly** `n` steps — with
  its executable counterpart `iterate step n x` (`mem_iterate`), the composition
  law `ReachIn.add` and the identification of "some positive number of steps"
  with `Relation.TransGen` (`transGen_iff_exists_reachIn`);
* `IsReturn step n x` (a return of `x` after `n > 0` steps), `IsPeriodic step x`,
  and the fact that the return times of a point are closed under addition
  (`IsReturn.add`);
* `periodOf step bound x` — the **search**: the least return time of `x` not
  exceeding `bound`, if there is one.  It is sound (`periodOf_isReturn`),
  minimal (`periodOf_min`) and complete up to the bound
  (`periodOf_eq_none_iff`, `isSome_periodOf`);
* `IsPeriodDivisor step d x` — `d` divides *every* return time of `x`, the
  divisibility form of the period of a point in the sense of Markov chains — and
  the transfer theorem `isPeriodDivisor_iff_of_connected`: **two points that
  reach each other have the same period divisors**, so periodicity is an
  invariant of a strongly connected component, not of a point.  Periodicity
  itself transfers likewise (`IsPeriodic.transfer`).

The Wikidata layer (`Wikidata.KB`):

* `KB.subPeriodOf` — the periodicity search along `subclass of`;
* `KB.periodicItems` — the items that lie on a `subclass of` cycle, computed in
  one pass over the closure table and characterised exactly
  (`KB.mem_periodicItems`): in a well-formed base they are precisely the periodic
  points of the hierarchy;
* `KB.mem_periodicItems_iff_mem_cyclicItems` — with no `subclass of` self-loops,
  the periodic items are exactly the cyclic items of the defect report, so the
  periodicity search refines the existing cycle detection by attaching a period
  to each item it finds.

`RequestProject.PeriodicityReport` runs the search over the downloaded corpus.
-/

namespace Wikidata
namespace Periodicity

variable {α : Type*}

/-! ### Walks of a given length -/

/-- `ReachIn step n x y`: the point `y` is reached from `x` by a walk of exactly
`n` steps of `step`. -/
inductive ReachIn (step : α → List α) : ℕ → α → α → Prop
  /-- The empty walk. -/
  | refl (x : α) : ReachIn step 0 x x
  /-- One more step at the end of a walk. -/
  | tail {n : ℕ} {x y z : α} : ReachIn step n x y → z ∈ step y → ReachIn step (n + 1) x z

/-- The points reachable in exactly `n` steps, computed. -/
def iterate [DecidableEq α] (step : α → List α) : ℕ → α → List α
  | 0, x => [x]
  | (n + 1), x => ((iterate step n x).flatMap step).dedup

theorem reachIn_zero_iff {step : α → List α} {x y : α} :
    ReachIn step 0 x y ↔ x = y := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact ReachIn.refl x

theorem reachIn_succ_iff {step : α → List α} {n : ℕ} {x z : α} :
    ReachIn step (n + 1) x z ↔ ∃ y, ReachIn step n x y ∧ z ∈ step y := by
  constructor
  · intro h; cases h with
    | tail hxy hz => exact ⟨_, hxy, hz⟩
  · rintro ⟨y, hxy, hz⟩; exact hxy.tail hz

/-- **The search step is faithful**: the computed list of points reachable in
`n` steps is exactly the set of endpoints of `n`-step walks. -/
theorem mem_iterate [DecidableEq α] {step : α → List α} {n : ℕ} {x y : α} :
    y ∈ iterate step n x ↔ ReachIn step n x y := by
  induction n generalizing y with
  | zero =>
      simp only [iterate, List.mem_singleton, reachIn_zero_iff]
      exact eq_comm
  | succ n ih =>
      simp only [iterate, List.mem_dedup, List.mem_flatMap, reachIn_succ_iff]
      constructor
      · rintro ⟨w, hw, hy⟩; exact ⟨w, ih.1 hw, hy⟩
      · rintro ⟨w, hw, hy⟩; exact ⟨w, ih.2 hw, hy⟩

theorem reachIn_one_iff {step : α → List α} {x y : α} :
    ReachIn step 1 x y ↔ y ∈ step x := by
  rw [reachIn_succ_iff]
  constructor
  · rintro ⟨w, hw, hy⟩; rwa [reachIn_zero_iff.1 hw]
  · intro hy; exact ⟨x, ReachIn.refl x, hy⟩

/-- Walks compose: `m` steps followed by `n` steps make `m + n` steps. -/
theorem ReachIn.add {step : α → List α} {m n : ℕ} {x y z : α}
    (hxy : ReachIn step m x y) (hyz : ReachIn step n y z) : ReachIn step (m + n) x z := by
  induction n generalizing z with
  | zero => rw [reachIn_zero_iff.1 hyz] at hxy; simpa using hxy
  | succ n ih =>
      obtain ⟨w, hw, hz⟩ := reachIn_succ_iff.1 hyz
      exact (ih hw).tail hz

/-- Positive-length walks are exactly the transitive closure of the step
relation. -/
theorem transGen_iff_exists_reachIn {step : α → List α} {x y : α} :
    Relation.TransGen (fun a b => b ∈ step a) x y ↔ ∃ n, 0 < n ∧ ReachIn step n x y := by
  constructor
  · intro h
    induction h with
    | single hxy => exact ⟨1, Nat.one_pos, reachIn_one_iff.2 hxy⟩
    | tail _ hbc ih =>
        obtain ⟨n, hn, hr⟩ := ih
        exact ⟨n + 1, Nat.succ_pos _, hr.tail hbc⟩
  · rintro ⟨n, hn, hr⟩
    induction n generalizing y with
    | zero => omega
    | succ n ih =>
        obtain ⟨w, hw, hy⟩ := reachIn_succ_iff.1 hr
        rcases Nat.eq_zero_or_pos n with rfl | hpos
        · exact Relation.TransGen.single (by rwa [← reachIn_zero_iff.1 hw] at hy)
        · exact (ih hpos hw).tail hy

/-! ### Return times -/

/-- `n > 0` steps take `x` back to itself. -/
def IsReturn (step : α → List α) (n : ℕ) (x : α) : Prop := 0 < n ∧ ReachIn step n x x

/-- A point is *periodic* when some positive number of steps returns to it, i.e.
when it lies on a cycle. -/
def IsPeriodic (step : α → List α) (x : α) : Prop := ∃ n, IsReturn step n x

/-- The return times of a point are closed under addition. -/
theorem IsReturn.add {step : α → List α} {m n : ℕ} {x : α}
    (hm : IsReturn step m x) (hn : IsReturn step n x) : IsReturn step (m + n) x :=
  ⟨Nat.add_pos_left hm.1 n, hm.2.add hn.2⟩

theorem isPeriodic_iff_transGen {step : α → List α} {x : α} :
    IsPeriodic step x ↔ Relation.TransGen (fun a b => b ∈ step a) x x := by
  rw [transGen_iff_exists_reachIn]
  exact ⟨fun ⟨n, hn⟩ => ⟨n, hn.1, hn.2⟩, fun ⟨n, hn, hr⟩ => ⟨n, hn, hr⟩⟩

/-! ### The search -/

/-- **The periodicity search**: the least `n` with `1 ≤ n ≤ bound` returning `x`
to itself, if there is one. -/
def periodOf [DecidableEq α] (step : α → List α) (bound : ℕ) (x : α) : Option ℕ :=
  (List.range' 1 bound).find? fun n => decide (x ∈ iterate step n x)

theorem periodOf_eq_some_iff [DecidableEq α] {step : α → List α} {bound n : ℕ} {x : α} :
    periodOf step bound x = some n ↔
      (IsReturn step n x ∧ n ≤ bound ∧ ∀ m, 0 < m → m < n → ¬ ReachIn step m x x) := by
  rw [periodOf, List.find?_eq_some_iff_append]
  constructor
  · rintro ⟨hn, as, bs, hsplit, hbefore⟩
    have hmem : n ∈ List.range' 1 bound := by
      rw [hsplit]; exact List.mem_append_right _ (List.mem_cons_self)
    rw [List.mem_range'_1] at hmem
    refine ⟨⟨hmem.1, mem_iterate.1 (by simpa using hn)⟩, by omega, ?_⟩
    intro m hm hmn hret
    have hmmem : m ∈ List.range' 1 bound := by
      rw [List.mem_range'_1]; omega
    rw [hsplit, List.mem_append] at hmmem
    rcases hmmem with h | h
    · have := hbefore m h
      simp only [Bool.not_eq_true', decide_eq_false_iff_not] at this
      exact this (mem_iterate.2 hret)
    · rcases List.mem_cons.1 h with rfl | h
      · omega
      · -- `List.range'` is strictly increasing, so everything after `n` is larger
        have hsorted : List.Pairwise (fun a b => a < b) (List.range' 1 bound) :=
          List.pairwise_lt_range'
        rw [hsplit] at hsorted
        have := (List.pairwise_append.1 hsorted).2.2
        exact absurd (List.rel_of_pairwise_cons ((List.pairwise_append.1 hsorted).2.1) h) (by omega)
  · rintro ⟨⟨hpos, hret⟩, hle, hmin⟩
    have hmem : n ∈ List.range' 1 bound := by rw [List.mem_range'_1]; omega
    obtain ⟨as, bs, hsplit⟩ := List.append_of_mem hmem
    refine ⟨by simpa using mem_iterate.2 hret, as, bs, hsplit, ?_⟩
    intro m hm
    have hmmem : m ∈ List.range' 1 bound := by rw [hsplit]; exact List.mem_append_left _ hm
    rw [List.mem_range'_1] at hmmem
    have hlt : m < n := by
      have hsorted : List.Pairwise (fun a b => a < b) (List.range' 1 bound) :=
        List.pairwise_lt_range'
      rw [hsplit] at hsorted
      exact (List.pairwise_append.1 hsorted).2.2 m hm n List.mem_cons_self
    simp only [Bool.not_eq_true', decide_eq_false_iff_not]
    intro hcontra
    exact hmin m (by omega) hlt (mem_iterate.1 hcontra)

/-- **Soundness of the search**: what it returns is a return time. -/
theorem periodOf_isReturn [DecidableEq α] {step : α → List α} {bound n : ℕ} {x : α}
    (h : periodOf step bound x = some n) : IsReturn step n x :=
  (periodOf_eq_some_iff.1 h).1

/-- **Minimality**: nothing smaller is a return time. -/
theorem periodOf_min [DecidableEq α] {step : α → List α} {bound n : ℕ} {x : α}
    (h : periodOf step bound x = some n) {m : ℕ} (hm : 0 < m) (hmn : m < n) :
    ¬ ReachIn step m x x :=
  (periodOf_eq_some_iff.1 h).2.2 m hm hmn

/-- **Completeness up to the bound**: a failed search means no return time at all
below the bound. -/
theorem periodOf_eq_none_iff [DecidableEq α] {step : α → List α} {bound : ℕ} {x : α} :
    periodOf step bound x = none ↔ ∀ n, IsReturn step n x → bound < n := by
  rw [periodOf, List.find?_eq_none]
  constructor
  · intro h n hn
    obtain ⟨hpos, hr⟩ := hn
    by_contra hle
    have hmem : n ∈ List.range' 1 bound := by rw [List.mem_range'_1]; omega
    exact (h n hmem) (by simpa using mem_iterate.2 hr)
  · intro h n hmem hcontra
    rw [List.mem_range'_1] at hmem
    obtain ⟨h1, h2⟩ := hmem
    simp only [decide_eq_true_eq] at hcontra
    have := h n ⟨h1, mem_iterate.1 hcontra⟩
    omega

/-- A return time within the bound is found. -/
theorem isSome_periodOf [DecidableEq α] {step : α → List α} {bound n : ℕ} {x : α}
    (hn : IsReturn step n x) (hle : n ≤ bound) : (periodOf step bound x).isSome := by
  rcases hopt : periodOf step bound x with _ | m
  · exact absurd (periodOf_eq_none_iff.1 hopt n hn) (by omega)
  · rfl

/-- A point with a period found by the search is periodic. -/
theorem isPeriodic_of_periodOf [DecidableEq α] {step : α → List α} {bound n : ℕ} {x : α}
    (h : periodOf step bound x = some n) : IsPeriodic step x :=
  ⟨n, periodOf_isReturn h⟩

/-! ### The period of a strongly connected component -/

/-- `d` divides every return time of `x`.  The largest such `d` is the *period*
of `x` in the sense of Markov chains; a point is *aperiodic* when only `1`
divides all its return times. -/
def IsPeriodDivisor (step : α → List α) (d : ℕ) (x : α) : Prop :=
  ∀ n, IsReturn step n x → d ∣ n

/-- Periodicity transfers along mutual reachability. -/
theorem IsPeriodic.transfer {step : α → List α} {a b : ℕ} {x y : α}
    (hxy : ReachIn step a x y) (hyx : ReachIn step b y x) (hx : IsPeriodic step x) :
    IsPeriodic step y := by
  obtain ⟨n, hn, hr⟩ := hx
  exact ⟨b + n + a, ⟨by omega, (hyx.add hr).add hxy⟩⟩

/-- **The period is a property of the component, not of the point**: if `x`
reaches `y` and `y` reaches `x`, then every divisor of all return times of `x`
divides all return times of `y`. -/
theorem isPeriodDivisor_transfer {step : α → List α} {a b d : ℕ} {x y : α}
    (hxy : ReachIn step a x y) (hyx : ReachIn step b y x)
    (hx : IsPeriodDivisor step d x) : IsPeriodDivisor step d y := by
  intro c hc
  rcases Nat.eq_zero_or_pos (a + b) with hab | hab
  · -- `x` and `y` are the same point
    have ha : a = 0 := by omega
    have hb : b = 0 := by omega
    subst ha; subst hb
    rw [reachIn_zero_iff.1 hxy] at hx
    exact hx c hc
  · have hround : IsReturn step (a + b) x := ⟨hab, hxy.add hyx⟩
    have hbig : IsReturn step (a + (c + b)) x :=
      ⟨by omega, hxy.add (hc.2.add hyx)⟩
    have h1 : d ∣ a + b := hx _ hround
    have h2 : d ∣ a + (c + b) := hx _ hbig
    have h3 : d ∣ (a + b) + c := by rwa [show (a + b) + c = a + (c + b) by omega]
    exact (Nat.dvd_add_right h1).1 h3

/-- Two mutually reachable points have exactly the same period divisors. -/
theorem isPeriodDivisor_iff_of_connected {step : α → List α} {a b d : ℕ} {x y : α}
    (hxy : ReachIn step a x y) (hyx : ReachIn step b y x) :
    IsPeriodDivisor step d x ↔ IsPeriodDivisor step d y :=
  ⟨isPeriodDivisor_transfer hxy hyx, isPeriodDivisor_transfer hyx hxy⟩

/-- **A phase certificate bounds the period from below.**  Suppose every step
inside the strongly connected component of `x` — that is, between points that
`x` reaches and that reach `x` back — advances a `ZMod d`-valued *phase* by one.
Then `d` divides every return time of `x`: the component is `d`-periodic.  This
is the converse direction to the search, which only ever exhibits return times. -/
theorem isPeriodDivisor_of_phase {step : α → List α} {d : ℕ} [NeZero d] {x : α}
    (phase : α → ZMod d)
    (hedge : ∀ y z, (∃ a, ReachIn step a x y) → (∃ b, ReachIn step b y x) →
        z ∈ step y → (∃ c, ReachIn step c z x) → phase z = phase y + 1) :
    IsPeriodDivisor step d x := by
  have key : ∀ n y, ReachIn step n x y → (∃ b, ReachIn step b y x) →
      phase y = phase x + (n : ZMod d) := by
    intro n
    induction n with
    | zero =>
        intro y hxy _
        rw [← reachIn_zero_iff.1 hxy]
        simp
    | succ n ih =>
        intro z hxz hzx
        obtain ⟨w, hw, hz⟩ := reachIn_succ_iff.1 hxz
        obtain ⟨b, hb⟩ := hzx
        have hwx : ∃ b', ReachIn step b' w x := ⟨1 + b, (reachIn_one_iff.2 hz).add hb⟩
        have hphw := ih w hw hwx
        rw [hedge w z ⟨n, hw⟩ hwx hz ⟨b, hb⟩, hphw]
        push_cast
        ring
  intro n hn
  have hx := key n x hn.2 ⟨0, ReachIn.refl x⟩
  have hzero : (n : ZMod d) = 0 := by
    have := hx.symm
    simpa using this
  exact (ZMod.natCast_eq_zero_iff n d).mp hzero

/-- **The return times of a point, exactly**: if `d` is a return time and
divides every return time, the return times are precisely the positive multiples
of `d`. -/
theorem isReturn_iff_multiple {step : α → List α} {d : ℕ} {x : α}
    (hd : IsReturn step d x) (hdiv : IsPeriodDivisor step d x) (n : ℕ) :
    IsReturn step n x ↔ ∃ k, 0 < k ∧ n = d * k := by
  constructor
  · intro hn
    obtain ⟨k, hk⟩ := hdiv n hn
    refine ⟨k, ?_, hk⟩
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · exfalso
      have hn0 : n = 0 := by simpa using hk
      exact absurd hn.1 (by omega)
    · exact hpos
  · rintro ⟨k, hk, rfl⟩
    induction k with
    | zero => omega
    | succ k ih =>
        rcases Nat.eq_zero_or_pos k with rfl | hpos
        · simpa using hd
        · have := (ih hpos).add hd
          rw [show d * k + d = d * (k + 1) by ring] at this
          exact this

/-- Everything divides the return times of a point that has none. -/
theorem isPeriodDivisor_of_not_isPeriodic {step : α → List α} {d : ℕ} {x : α}
    (h : ¬ IsPeriodic step x) : IsPeriodDivisor step d x := by
  intro n hn
  exact absurd ⟨n, hn⟩ h

end Periodicity

/-! ### The periodicity search on a knowledge base -/

namespace KB

open Periodicity

variable (kb : KB)

/-- The periodicity search along `subclass of`: the length of the shortest
`subclass of` cycle through an item, if there is one of length at most `bound`. -/
def subPeriodOf (bound : ℕ) (x : Qid) : Option ℕ := periodOf kb.supersL bound x

/-- Does the item lie on a `subclass of` cycle?  Decided against a closure
table: some direct superclass of the item has the item back among *its*
superclasses. -/
def onSubCycleT (T : List (Qid × Finset Qid)) (x : Qid) : Bool :=
  (kb.supersL x).any fun y => kb.isSubclassOfT T y x

/-- The items on a `subclass of` cycle, against a given closure table. -/
def periodicItemsT (T : List (Qid × Finset Qid)) : List Qid :=
  kb.items.filter (kb.onSubCycleT T)

/-- **The periodic items of the class hierarchy**, found in one pass over the
closure table. -/
def periodicItems : List Qid := kb.periodicItemsT kb.closureTable

/-- The items that lie on no `subclass of` cycle, against a given closure
table. -/
def aperiodicItemsT (T : List (Qid × Finset Qid)) : List Qid :=
  kb.items.filter (fun x => !kb.onSubCycleT T x)

/-- The aperiodic items of the class hierarchy, found in the same pass. -/
def aperiodicItems : List Qid := kb.aperiodicItemsT kb.closureTable

/-- An item is aperiodic exactly when it is not periodic. -/
theorem mem_aperiodicItems {x : Qid} :
    x ∈ kb.aperiodicItems ↔ x ∈ kb.items ∧ x ∉ kb.periodicItems := by
  simp only [aperiodicItems, aperiodicItemsT, periodicItems, periodicItemsT, List.mem_filter,
    Bool.not_eq_true', not_and]
  constructor
  · rintro ⟨hx, hcyc⟩
    exact ⟨hx, fun _ => by simp [hcyc]⟩
  · rintro ⟨hx, hcyc⟩
    exact ⟨hx, by simpa using hcyc hx⟩

/-- The phase check of a `subclass of` component: along every `subclass of`
statement inside the strongly connected component of `x`, the phase advances by
one.  Everything is decided against one closure table. -/
def phaseOkBT (T : List (Qid × Finset Qid)) (x : Qid) (d : ℕ) [NeZero d]
    (phase : Qid → ZMod d) : Bool :=
  kb.sub.all fun p =>
    !(kb.isSubclassOfT T x p.1 && kb.isSubclassOfT T p.1 x && kb.isSubclassOfT T p.2 x) ||
      (phase p.2 == phase p.1 + 1)

/-- The phase check against the closure table of the base itself. -/
def phaseOkB (x : Qid) (d : ℕ) [NeZero d] (phase : Qid → ZMod d) : Bool :=
  kb.phaseOkBT kb.closureTable x d phase

/-- **The period of a `subclass of` component, certified from above.**  If the
phase check succeeds then every `subclass of` cycle through `x` has length
divisible by `d`.  Together with the periodicity search, which exhibits a cycle
of length `d`, this pins the period of the component down exactly. -/
theorem isPeriodDivisor_of_phaseOkB (hwf : kb.wellFormed = true) {x : Qid} {d : ℕ} [NeZero d]
    {phase : Qid → ZMod d} (h : kb.phaseOkB x d phase = true) :
    IsPeriodDivisor kb.supersL d x := by
  have hstep : ∀ {u v : Qid}, v ∈ kb.supersL u ↔ kb.Sub u v := mem_supersL
  have hreach : ∀ {u v : Qid}, (∃ n, ReachIn kb.supersL n u v) ↔ kb.isSubclassOf u v = true := by
    intro u v
    rw [isSubclassOf_iff hwf]
    constructor
    · rintro ⟨n, hn⟩
      induction n generalizing v with
      | zero => rw [← reachIn_zero_iff.1 hn]
      | succ n ih =>
          obtain ⟨w, hw, hv⟩ := reachIn_succ_iff.1 hn
          exact (ih hw).tail (hstep.1 hv)
    · intro hcl
      induction hcl with
      | refl => exact ⟨0, ReachIn.refl u⟩
      | tail _ hbc ih =>
          obtain ⟨n, hn⟩ := ih
          exact ⟨n + 1, hn.tail (hstep.2 hbc)⟩
  refine isPeriodDivisor_of_phase phase ?_
  intro y z hxy hyx hz hzx
  simp only [phaseOkB, phaseOkBT, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    Bool.and_eq_false_iff, beq_iff_eq, isSubclassOfT_closureTable] at h
  have hyz : (y, z) ∈ kb.sub := hstep.1 hz
  rcases h (y, z) hyz with hfalse | heq
  · exfalso
    rcases hfalse with (hf | hf) | hf
    · exact absurd (hreach.1 hxy) (by simp [hf])
    · exact absurd (hreach.1 hyx) (by simp [hf])
    · exact absurd (hreach.1 hzx) (by simp [hf])
  · exact heq

/-- **The search is exactly right**: in a well-formed knowledge base the computed
periodic items are precisely the periodic points of the `subclass of` graph. -/
theorem mem_periodicItems (hwf : kb.wellFormed = true) {x : Qid} :
    x ∈ kb.periodicItems ↔ IsPeriodic kb.supersL x := by
  have hstep : (fun a b => b ∈ kb.supersL a) = kb.Sub := by
    funext a b; exact propext mem_supersL
  rw [periodicItems, periodicItemsT, List.mem_filter, isPeriodic_iff_transGen, hstep,
    Relation.TransGen.head'_iff]
  simp only [onSubCycleT, List.any_eq_true, isSubclassOfT_closureTable]
  constructor
  · rintro ⟨-, y, hy, hyx⟩
    exact ⟨y, mem_supersL.1 hy, (isSubclassOf_iff hwf y x).1 hyx⟩
  · rintro ⟨y, hy, hyx⟩
    exact ⟨(wf_sub hwf hy).1, y, mem_supersL.2 hy, (isSubclassOf_iff hwf y x).2 hyx⟩

/-- A periodic item is an item. -/
theorem mem_items_of_isPeriodic (hwf : kb.wellFormed = true) {x : Qid}
    (h : IsPeriodic kb.supersL x) : x ∈ kb.items :=
  List.mem_of_mem_filter ((kb.mem_periodicItems hwf).2 h)

/-- With no `subclass of` self-loops, the periodicity search finds exactly the
items the cycle detection of the defect report finds — but it also computes the
length of the cycle. -/
theorem mem_periodicItems_iff_mem_cyclicItems (hwf : kb.wellFormed = true)
    (hloop : ∀ a : Qid, ¬ kb.Sub a a) {x : Qid} :
    x ∈ kb.periodicItems ↔ x ∈ kb.cyclicItems := by
  have hstep : (fun a b => b ∈ kb.supersL a) = kb.Sub := by
    funext a b; exact propext mem_supersL
  rw [kb.mem_periodicItems hwf, isPeriodic_iff_transGen, mem_cyclicItems, hstep,
    Relation.TransGen.head'_iff]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have hne : y ≠ x := by rintro rfl; exact hloop _ hy
    exact ⟨(wf_sub hwf hy).1, y, (wf_sub hwf hy).2, fun h => hne h.symm,
      (isSubclassOf_iff hwf x y).2 (Relation.ReflTransGen.single hy),
      (isSubclassOf_iff hwf y x).2 hyx⟩
  · rintro ⟨-, b, -, hne, h1, h2⟩
    have hxb := (isSubclassOf_iff hwf x b).1 h1
    have hbx := (isSubclassOf_iff hwf b x).1 h2
    rcases Relation.reflTransGen_iff_eq_or_transGen.1 hxb with rfl | htg
    · exact absurd rfl hne
    · obtain ⟨y, hy, hyb⟩ := Relation.TransGen.head'_iff.1 htg
      exact ⟨y, hy, hyb.trans hbx⟩

end KB

/-! ### A worked fragment: the shortest cycle is not the period

Four classes with a two-step cycle and a three-step cycle through the same item.
The periodicity search returns `2`, the length of the shortest cycle, but `3` is
a return time as well, so the only number dividing *every* return time is `1`:
the item is aperiodic even though it lies on a cycle of length `2`.  The
identifiers `Q1`–`Q4` are the placeholders of the hand-written illustrations of
this library, not references to Wikidata. -/

namespace PeriodicityExample

open Periodicity

/-- The item both cycles run through. -/
def a : Qid := .wd "Q1"
/-- The other item of the two-step cycle. -/
def b : Qid := .wd "Q2"
/-- The first further item of the three-step cycle. -/
def c : Qid := .wd "Q3"
/-- The second further item of the three-step cycle. -/
def d : Qid := .wd "Q4"

/-- `a ⊑ b ⊑ a` and `a ⊑ c ⊑ d ⊑ a`. -/
def kb : KB where
  name := "two cycles"
  items := [a, b, c, d]
  sub := [(a, b), (b, a), (a, c), (c, d), (d, a)]

theorem kb_wellFormed : kb.wellFormed = true := by decide

/-- The search finds the shortest cycle through `a`: two steps. -/
theorem a_subPeriod : kb.subPeriodOf 10 a = some 2 := by decide

/-- Three steps also return to `a`. -/
theorem a_return_three : IsReturn kb.supersL 3 a :=
  ⟨by norm_num, mem_iterate.1 (by decide)⟩

/-- So the shortest cycle length does *not* divide all return times. -/
theorem a_not_periodDivisor_two : ¬ IsPeriodDivisor kb.supersL 2 a := by
  intro h
  have := h 3 a_return_three
  omega

/-- **The item is aperiodic**: only `1` divides all its return times. -/
theorem a_periodDivisor_eq_one {n : ℕ} (h : IsPeriodDivisor kb.supersL n a) : n = 1 := by
  have h2 : n ∣ 2 := h 2 ⟨by norm_num, mem_iterate.1 (by decide)⟩
  have h3 : n ∣ 3 := h 3 a_return_three
  have h1 : n ∣ 1 := by simpa using Nat.dvd_sub h3 h2
  exact Nat.dvd_one.mp h1

/-- And so is `b`, by the transfer theorem alone: it reaches `a` and `a` reaches
`b`. -/
theorem b_periodDivisor_eq_one {n : ℕ} (h : IsPeriodDivisor kb.supersL n b) : n = 1 := by
  refine a_periodDivisor_eq_one (n := n) ?_
  refine (isPeriodDivisor_iff_of_connected (x := b) (y := a) (a := 1) (b := 1) ?_ ?_).1 h
  · exact reachIn_one_iff.2 (by decide)
  · exact reachIn_one_iff.2 (by decide)

/-- Both are periodic points of the hierarchy, and the search says so. -/
theorem periodicItems_eq : kb.periodicItems = [a, b, c, d] := by decide

end PeriodicityExample


end Wikidata
