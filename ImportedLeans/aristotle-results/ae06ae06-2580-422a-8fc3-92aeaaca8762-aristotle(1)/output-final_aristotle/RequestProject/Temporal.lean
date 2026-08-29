import RequestProject.Engine

/-!
# time-qualified statements: `start time` (P580) and `end time` (P582)

Wikidata statements are frequently qualified by a *validity interval*: the
qualifiers `start time` (P580) and `end time` (P582) say when the statement was
(or is) true.  A query is then answered *at a point in time*: the ontology one
actually reasons with is the **snapshot** of the knowledge base at that time.

This file adds that layer.

* `Wikidata.TimeInterval` — an optional start and an optional end, with
  membership `Mem`, its decision procedure `memB`, intersection, inclusion and
  disjointness.
* `Wikidata.TimeKB` — a time-qualified knowledge base: items, levels, and `subclass
  of` / `instance of` links each carrying a validity interval.
* `Wikidata.TimeKB.snapshot` — the ordinary `KB` obtained by keeping exactly the
  links valid at a given time, and `Wikidata.TimeKB.full`, the base that forgets the
  intervals.

The two main results are:

* `Wikidata.KB.valid_of_subset` — a knowledge base obtained from a valid one by
  *deleting* statements is itself valid (levels, acyclicity and disjointness are
  all inherited downwards), hence
  `Wikidata.TimeKB.valid_snapshot` — **every snapshot of a coherent time-qualified
  base is a valid ontology**, so all the theorems of `RequestProject.Core` apply
  to it, at every point in time; and
* `Wikidata.TimeKB.isSubclassOf_snapshot_le` / `isInstanceOf_snapshot_le` — nothing
  is derivable at a point in time that is not derivable from the whole base, so a
  snapshot never invents facts.

Finally, statements valid at *all* times (interval `TimeInterval.always`) survive
every snapshot, and a statement whose interval is *incoherent* (end before start)
is invisible at every time.
-/

namespace Wikidata

/-- Points in time are modelled by integers (think: a year).

A validity interval, given by the qualifiers `start time` (P580) and
`end time` (P582); `none` means the qualifier is absent (unbounded on that side). -/
structure TimeInterval where
  /-- The `start time` (P580) qualifier, if present. -/
  start : Option ℤ := none
  /-- The `end time` (P582) qualifier, if present. -/
  stop : Option ℤ := none
deriving DecidableEq, Repr, Inhabited

namespace TimeInterval

/-- The interval carrying no qualifier at all: valid at every time. -/
def always : TimeInterval := {}

/-- A time lies in an interval when it is after the start (if any) and before the
end (if any). -/
def Mem (i : TimeInterval) (t : ℤ) : Prop :=
  (∀ a, i.start = some a → a ≤ t) ∧ (∀ b, i.stop = some b → t ≤ b)

/-- The decision procedure for `TimeInterval.Mem`. -/
def memB (i : TimeInterval) (t : ℤ) : Bool :=
  (match i.start with | none => true | some a => decide (a ≤ t)) &&
  (match i.stop with | none => true | some b => decide (t ≤ b))

@[simp] theorem memB_iff {i : TimeInterval} {t : ℤ} : i.memB t = true ↔ i.Mem t := by
  cases i with
  | mk s f =>
    cases s <;> cases f <;> simp [memB, Mem]

theorem mem_always (t : ℤ) : always.Mem t := by simp [always, Mem]

@[simp] theorem memB_always (t : ℤ) : always.memB t = true := by simp [always, memB]

/-- An interval is *coherent* when its end does not precede its start. -/
def Coherent (i : TimeInterval) : Prop := ∀ a b, i.start = some a → i.stop = some b → a ≤ b

/-- A coherent interval contains some point in time. -/
theorem exists_mem_of_coherent {i : TimeInterval} (h : i.Coherent) : ∃ t, i.Mem t := by
  cases i with
  | mk s f =>
    cases s with
    | none =>
      cases f with
      | none => exact ⟨0, by simp [Mem]⟩
      | some b => exact ⟨b, by simp [Mem]⟩
    | some a =>
      refine ⟨a, ?_⟩
      cases f with
      | none => simp [Mem]
      | some b =>
        have : a ≤ b := h a b rfl rfl
        simp [Mem, this]

/-- An incoherent interval — one whose `end time` precedes its `start time` —
contains no point in time at all. -/
theorem not_mem_of_incoherent {i : TimeInterval} (h : ¬ i.Coherent) (t : ℤ) : ¬ i.Mem t := by
  intro ht
  apply h
  intro a b ha hb
  exact le_trans (ht.1 a ha) (ht.2 b hb)

/-- Inclusion of intervals. -/
def Sub (i j : TimeInterval) : Prop := ∀ t, i.Mem t → j.Mem t

theorem sub_refl (i : TimeInterval) : i.Sub i := fun _ h => h

theorem sub_trans {i j k : TimeInterval} (hij : i.Sub j) (hjk : j.Sub k) : i.Sub k :=
  fun t h => hjk t (hij t h)

theorem sub_always (i : TimeInterval) : i.Sub always := fun t _ => mem_always t

/-- Two intervals are disjoint when no time lies in both. -/
def Disj (i j : TimeInterval) : Prop := ∀ t, ¬ (i.Mem t ∧ j.Mem t)

theorem disj_comm {i j : TimeInterval} (h : i.Disj j) : j.Disj i :=
  fun t ht => h t ⟨ht.2, ht.1⟩

/-- The later of two optional lower bounds. -/
def maxStart : Option ℤ → Option ℤ → Option ℤ
  | none, y => y
  | x, none => x
  | some a, some b => some (max a b)

/-- The earlier of two optional upper bounds. -/
def minStop : Option ℤ → Option ℤ → Option ℤ
  | none, y => y
  | x, none => x
  | some a, some b => some (min a b)

/-- The intersection of two validity intervals. -/
def inter (i j : TimeInterval) : TimeInterval :=
  ⟨maxStart i.start j.start, minStop i.stop j.stop⟩

theorem memB_inter (i j : TimeInterval) (t : ℤ) :
    (i.inter j).memB t = (i.memB t && j.memB t) := by
  cases i with
  | mk s₁ f₁ =>
    cases j with
    | mk s₂ f₂ =>
      cases s₁ <;> cases s₂ <;> cases f₁ <;> cases f₂ <;>
        simp [inter, memB, maxStart, minStop, Bool.and_assoc, Bool.and_left_comm, Bool.and_comm]

@[simp] theorem mem_inter {i j : TimeInterval} {t : ℤ} :
    (i.inter j).Mem t ↔ i.Mem t ∧ j.Mem t := by
  rw [← memB_iff, ← memB_iff, ← memB_iff, memB_inter, Bool.and_eq_true]

/-- Two intervals are disjoint exactly when their intersection is incoherent. -/
theorem disj_iff_inter_incoherent {i j : TimeInterval} :
    i.Disj j ↔ ¬ (i.inter j).Coherent := by
  constructor
  · intro h hc
    obtain ⟨t, ht⟩ := exists_mem_of_coherent hc
    exact h t (mem_inter.1 ht)
  · intro h t ht
    exact not_mem_of_incoherent h t (mem_inter.2 ht)

end TimeInterval

/-- A time-qualified link between two items: a `subclass of` or `instance of`
statement together with its validity interval. -/
structure TLink where
  /-- The subject of the statement. -/
  src : Qid
  /-- The object of the statement. -/
  dst : Qid
  /-- The validity interval given by the P580/P582 qualifiers. -/
  iv : TimeInterval := TimeInterval.always
deriving DecidableEq, Repr, Inhabited

/-- A time-qualified knowledge base: as a `KB`, but every `subclass of` and
`instance of` statement carries a validity interval. -/
structure TimeKB where
  /-- A human readable name. -/
  name : String := "temporal ontology"
  /-- The items. -/
  items : List Qid
  /-- The metaclass levels. -/
  levels : List (Qid × ℕ) := []
  /-- time-qualified `subclass of` (P279) statements. -/
  tsub : List TLink := []
  /-- time-qualified `instance of` (P31) statements. -/
  tinst : List TLink := []
  /-- Declared disjointness between classes. -/
  disj : List (Qid × Qid) := []
deriving Repr, DecidableEq, Inhabited

namespace KB

/-- Deleting statements from a valid knowledge base leaves it valid: the level
discipline, acyclicity and the disjointness declarations are all inherited by
sub-bases. -/
theorem valid_of_subset {kb kb' : KB} (hitems : kb'.items = kb.items)
    (hlev : kb'.levels = kb.levels)
    (hsub : ∀ x ∈ kb'.sub, x ∈ kb.sub) (hinst : ∀ x ∈ kb'.inst, x ∈ kb.inst)
    (hdisj : ∀ x ∈ kb'.disj, x ∈ kb.disj) (hv : kb.valid = true) : kb'.valid = true := by
  have hwf : kb.wellFormed = true := valid_wellFormed hv
  have hwf' : kb'.wellFormed = true := by
    simp only [wellFormed, Bool.and_eq_true, List.all_eq_true] at hwf ⊢
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro x hx
      have := hwf.1.1 x (hsub x (by simpa using hx))
      simpa [hitems] using this
    · intro x hx
      have := hwf.1.2 x (hinst x (by simpa using hx))
      simpa [hitems] using this
    · intro x hx
      have := hwf.2 x (hdisj x (by simpa using hx))
      simpa [hitems] using this
  -- the derived subclass relation shrinks
  have hlevelOf : ∀ q, kb'.levelOf q = kb.levelOf q := by
    intro q; simp [levelOf, hlev]
  have hsubrel : ∀ {a b}, kb'.Sub a b → kb.Sub a b := by
    intro a b h; exact hsub _ h
  have hmono : ∀ {a b}, kb'.isSubclassOf a b = true → kb.isSubclassOf a b = true := by
    intro a b h
    rw [isSubclassOf_iff hwf]
    rw [isSubclassOf_iff hwf'] at h
    exact h.mono (fun _ _ hxy => hsubrel hxy)
  have hmonoI : ∀ {a c}, kb'.isInstanceOf a c = true → kb.isInstanceOf a c = true := by
    intro a c h
    rw [isInstanceOf_iff hwf]
    rw [isInstanceOf_iff hwf'] at h
    obtain ⟨d, hd, hdc⟩ := h
    exact ⟨d, hinst _ hd, hdc.mono (fun _ _ hxy => hsubrel hxy)⟩
  have hlv : kb'.levelsOk = true := by
    have h := valid_levelsOk hv
    simp only [levelsOk, Bool.and_eq_true, List.all_eq_true] at h ⊢
    refine ⟨?_, ?_⟩
    · intro x hx
      have := h.1 x (hinst x (by simpa using hx))
      simpa [hlevelOf] using this
    · intro x hx
      have := h.2 x (hsub x (by simpa using hx))
      simpa [hlevelOf] using this
  have hac : kb'.acyclic = true := by
    have h := valid_acyclic hv
    simp only [acyclic, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
      Bool.and_eq_false_iff, beq_iff_eq] at h ⊢
    intro a ha b hb
    have ha' : a ∈ kb.items := by rwa [hitems] at ha
    have hb' : b ∈ kb.items := by rwa [hitems] at hb
    by_cases hab : kb'.isSubclassOf a b = true
    · by_cases hba : kb'.isSubclassOf b a = true
      · rcases h a ha' b hb' with h₁ | h₁
        · rcases h₁ with h₁ | h₁
          · exact absurd (hmono hab) (by simp [h₁])
          · exact absurd (hmono hba) (by simp [h₁])
        · exact Or.inr h₁
      · exact Or.inl (Or.inr (by simpa using hba))
    · exact Or.inl (Or.inl (by simpa using hab))
  have hdj : kb'.disjointOk = true := by
    have h := valid_disjointOk hv
    simp only [disjointOk, List.all_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff] at h ⊢
    intro x hx a ha
    have hx' := hdisj x (by simpa using hx)
    have ha' : a ∈ kb.items := by rwa [hitems] at ha
    rcases h x hx' a ha' with h₁ | h₁
    · by_cases hh : kb'.isInstanceOf a x.1 = true
      · exact absurd (hmonoI hh) (by simp [h₁])
      · exact Or.inl (by simpa using hh)
    · by_cases hh : kb'.isInstanceOf a x.2 = true
      · exact absurd (hmonoI hh) (by simp [h₁])
      · exact Or.inr (by simpa using hh)
  simp [valid, hwf', hlv, hac, hdj]

end KB

namespace TimeKB

variable (T : TimeKB)

/-- The knowledge base that forgets all the validity intervals: every
time-qualified statement is asserted outright. -/
def full : KB where
  name := T.name
  items := T.items
  levels := T.levels
  sub := T.tsub.map (fun l => (l.src, l.dst))
  inst := T.tinst.map (fun l => (l.src, l.dst))
  disj := T.disj

/-- The snapshot of the base at a point in time: the ordinary knowledge base
consisting of exactly the statements valid at that time. -/
def snapshot (t : ℤ) : KB where
  name := T.name
  items := T.items
  levels := T.levels
  sub := (T.tsub.filter (fun l => l.iv.memB t)).map (fun l => (l.src, l.dst))
  inst := (T.tinst.filter (fun l => l.iv.memB t)).map (fun l => (l.src, l.dst))
  disj := T.disj

@[simp] theorem snapshot_items (t : ℤ) : (T.snapshot t).items = T.items := rfl

@[simp] theorem full_items : T.full.items = T.items := rfl

theorem snapshot_sub_subset {t : ℤ} {x : Qid × Qid} (h : x ∈ (T.snapshot t).sub) :
    x ∈ T.full.sub := by
  simp only [snapshot, full, List.mem_map, List.mem_filter] at h ⊢
  obtain ⟨l, ⟨hl, _⟩, rfl⟩ := h
  exact ⟨l, hl, rfl⟩

theorem snapshot_inst_subset {t : ℤ} {x : Qid × Qid} (h : x ∈ (T.snapshot t).inst) :
    x ∈ T.full.inst := by
  simp only [snapshot, full, List.mem_map, List.mem_filter] at h ⊢
  obtain ⟨l, ⟨hl, _⟩, rfl⟩ := h
  exact ⟨l, hl, rfl⟩

/-- **Every snapshot of a coherent time-qualified base is a valid ontology.**
Consequently all the theorems of `RequestProject.Core` hold of the base at every
point in time. -/
theorem valid_snapshot (hv : T.full.valid = true) (t : ℤ) : (T.snapshot t).valid = true :=
  KB.valid_of_subset (kb := T.full) (kb' := T.snapshot t) rfl rfl
    (fun _ h => T.snapshot_sub_subset h) (fun _ h => T.snapshot_inst_subset h) (fun _ h => h) hv

/-- A snapshot never invents subclass facts. -/
theorem isSubclassOf_snapshot_le (hv : T.full.valid = true) {t : ℤ} {a b : Qid}
    (h : (T.snapshot t).isSubclassOf a b = true) : T.full.isSubclassOf a b = true := by
  have hwf : T.full.wellFormed = true := KB.valid_wellFormed hv
  have hwf' : (T.snapshot t).wellFormed = true :=
    KB.valid_wellFormed (T.valid_snapshot hv t)
  rw [KB.isSubclassOf_iff hwf]
  rw [KB.isSubclassOf_iff hwf'] at h
  exact h.mono (fun _ _ hxy => T.snapshot_sub_subset hxy)

/-- A snapshot never invents instance facts. -/
theorem isInstanceOf_snapshot_le (hv : T.full.valid = true) {t : ℤ} {a c : Qid}
    (h : (T.snapshot t).isInstanceOf a c = true) : T.full.isInstanceOf a c = true := by
  have hwf : T.full.wellFormed = true := KB.valid_wellFormed hv
  have hwf' : (T.snapshot t).wellFormed = true :=
    KB.valid_wellFormed (T.valid_snapshot hv t)
  rw [KB.isInstanceOf_iff hwf]
  rw [KB.isInstanceOf_iff hwf'] at h
  obtain ⟨d, hd, hdc⟩ := h
  exact ⟨d, T.snapshot_inst_subset hd, hdc.mono (fun _ _ hxy => T.snapshot_sub_subset hxy)⟩

/-- A statement carrying no time qualifiers appears in every snapshot. -/
theorem mem_snapshot_sub_of_always {l : TLink} (hl : l ∈ T.tsub)
    (hiv : l.iv = TimeInterval.always) (t : ℤ) : (l.src, l.dst) ∈ (T.snapshot t).sub := by
  simp only [snapshot, List.mem_map, List.mem_filter]
  exact ⟨l, ⟨hl, by simp [hiv]⟩, rfl⟩

/-- A statement whose interval is incoherent appears in no snapshot. -/
theorem not_mem_snapshot_of_incoherent {l : TLink} (h : ¬ l.iv.Coherent) (t : ℤ) :
    l ∉ T.tsub.filter (fun l => l.iv.memB t) := by
  intro hmem
  rw [List.mem_filter] at hmem
  exact TimeInterval.not_mem_of_incoherent h t (TimeInterval.memB_iff.1 hmem.2)

/-! ### Single-valued-at-each-time statements

A property such as `country` may take different values at different times without
violating the single-value constraint, *provided* the validity intervals of the
differing values are disjoint. -/

/-- The statements of a subject that are valid at a given time. -/
def instAt (t : ℤ) (a : Qid) : List Qid :=
  ((T.tinst.filter (fun l => l.src == a && l.iv.memB t)).map (fun l => l.dst))

/-- A list of time-qualified links is *functional over time* when at each moment
it assigns at most one value to each subject. -/
def FunctionalOverTime (ls : List TLink) : Prop :=
  ∀ t, ∀ l ∈ ls, ∀ l' ∈ ls, l.src = l'.src → l.iv.Mem t → l'.iv.Mem t → l.dst = l'.dst

/-- Being functional over time is exactly the statement that any two links of the
same subject with different values have disjoint validity intervals. -/
theorem functionalOverTime_iff (ls : List TLink) :
    FunctionalOverTime ls ↔
      ∀ l ∈ ls, ∀ l' ∈ ls, l.src = l'.src → l.dst ≠ l'.dst → l.iv.Disj l'.iv := by
  constructor
  · intro h l hl l' hl' hsrc hdst t ht
    exact hdst (h t l hl l' hl' hsrc ht.1 ht.2)
  · intro h t l hl l' hl' hsrc hlt hl't
    by_contra hdst
    exact h l hl l' hl' hsrc hdst t ⟨hlt, hl't⟩

/-- If the statements are functional over time then every snapshot really does
assign at most one direct value per subject. -/
theorem instAt_subsingleton (h : FunctionalOverTime T.tinst) (t : ℤ) (a : Qid)
    {c d : Qid} (hc : c ∈ T.instAt t a) (hd : d ∈ T.instAt t a) : c = d := by
  simp only [instAt, List.mem_map, List.mem_filter, Bool.and_eq_true, beq_iff_eq] at hc hd
  obtain ⟨l, ⟨hl, hlsrc, hlt⟩, rfl⟩ := hc
  obtain ⟨l', ⟨hl', hl'src, hl't⟩, rfl⟩ := hd
  exact h t l hl l' hl' (by rw [hlsrc, hl'src]) (TimeInterval.memB_iff.1 hlt)
    (TimeInterval.memB_iff.1 hl't)

end TimeKB

/-! ### A worked fragment

Berlin (Q64) is an instance of *city* (Q515) at all times, was located in East
Germany (Q16957) from 1949 to 1990 and is located in Germany (Q183) from 1990 on;
*East Germany* was a *sovereign state* (Q3624078) only between 1949 and 1990. -/

namespace TemporalExample

open Wikidata

/-- Berlin. -/
def berlin : Qid := .wd "Q64"
/-- The class *city*. -/
def city : Qid := .wd "Q515"
/-- The class *sovereign state*. -/
def state : Qid := .wd "Q3624078"
/-- East Germany. -/
def gdr : Qid := .wd "Q16957"
/-- Germany. -/
def germany : Qid := .wd "Q183"
/-- The class *human settlement*. -/
def settlement : Qid := .wd "Q486972"
/-- The class *former country*. -/
def formerCountry : Qid := .wd "Q3024240"

/-- A small time-qualified fragment of Wikidata. -/
def frag : TimeKB where
  name := "temporal fragment"
  items := [berlin, city, state, gdr, germany, settlement, formerCountry]
  levels := [(berlin, 0), (city, 1), (state, 1), (gdr, 0), (germany, 0), (settlement, 1),
    (formerCountry, 1)]
  tsub := [⟨city, settlement, TimeInterval.always⟩]
  tinst :=
    [⟨berlin, city, TimeInterval.always⟩,
     ⟨gdr, state, ⟨some 1949, some 1990⟩⟩,
     ⟨gdr, formerCountry, ⟨some 1990, none⟩⟩,
     ⟨germany, state, ⟨some 1871, none⟩⟩]

/-- The same fragment with the end of East Germany recorded as 1989 instead, so
that the two classifications of East Germany no longer overlap. -/
def fragFixed : TimeKB :=
  { frag with
    tinst :=
      [⟨berlin, city, TimeInterval.always⟩,
       ⟨gdr, state, ⟨some 1949, some 1989⟩⟩,
       ⟨gdr, formerCountry, ⟨some 1990, none⟩⟩,
       ⟨germany, state, ⟨some 1871, none⟩⟩] }

/-- The fragment, with the intervals forgotten, is a valid ontology. -/
theorem frag_full_valid : frag.full.valid = true := by decide

/-- Hence so is every snapshot of it. -/
theorem frag_snapshot_valid (t : ℤ) : (frag.snapshot t).valid = true :=
  frag.valid_snapshot frag_full_valid t

/-- In 1980 East Germany was a sovereign state. -/
theorem gdr_state_1980 : (frag.snapshot 1980).isInstanceOf gdr state = true := by decide

/-- In 2000 it was not. -/
theorem gdr_not_state_2000 : (frag.snapshot 2000).isInstanceOf gdr state = false := by decide

/-- Nor was it in 1900. -/
theorem gdr_not_state_1900 : (frag.snapshot 1900).isInstanceOf gdr state = false := by decide

/-- Germany, on the other hand, is a sovereign state in 2000 … -/
theorem germany_state_2000 : (frag.snapshot 2000).isInstanceOf germany state = true := by decide

/-- … and already was in 1980. -/
theorem germany_state_1980 : (frag.snapshot 1980).isInstanceOf germany state = true := by decide

/-- Berlin is a *human settlement* at every one of these times, by inheritance
through the unqualified `subclass of` statement. -/
theorem berlin_settlement (t : ℤ) : (frag.snapshot t).isInstanceOf berlin settlement = true := by
  have hmem : (city, settlement) ∈ (frag.snapshot t).sub :=
    frag.mem_snapshot_sub_of_always (l := ⟨city, settlement, TimeInterval.always⟩) (by simp [frag])
      rfl t
  have hmemi : (berlin, city) ∈ (frag.snapshot t).inst := by
    simp only [TimeKB.snapshot, frag, List.mem_map, List.mem_filter]
    exact ⟨⟨berlin, city, TimeInterval.always⟩, ⟨by simp, by simp⟩, rfl⟩
  have hwf' : (frag.snapshot t).wellFormed = true :=
    KB.valid_wellFormed (frag_snapshot_valid t)
  have hsub : (frag.snapshot t).isSubclassOf city settlement = true := by
    rw [KB.isSubclassOf_iff hwf']
    exact Relation.ReflTransGen.single hmem
  simp only [KB.isInstanceOf, List.any_eq_true]
  exact ⟨city, KB.mem_directClassesL.2 hmemi, hsub⟩

/-- In 1990 East Germany is recorded both as a sovereign state and as a former
country, so the fragment is **not** functional over time: the two intervals
overlap. -/
theorem frag_not_functional : ¬ TimeKB.FunctionalOverTime frag.tinst := by
  intro h
  have h1 : (⟨gdr, state, ⟨some 1949, some 1990⟩⟩ : TLink) ∈ frag.tinst := by simp [frag]
  have h2 : (⟨gdr, formerCountry, ⟨some 1990, none⟩⟩ : TLink) ∈ frag.tinst := by simp [frag]
  have := h 1990 _ h1 _ h2 rfl (by simp [TimeInterval.Mem]) (by simp [TimeInterval.Mem])
  simp [state, formerCountry] at this

/-- With the end time corrected to 1989 the statements *are* functional over
time: at each moment every item has at most one directly asserted class. -/
theorem fragFixed_functional : TimeKB.FunctionalOverTime fragFixed.tinst := by
  intro t l hl l' hl' hsrc hlt hl't
  simp only [fragFixed, frag] at hl hl'
  fin_cases hl <;> fin_cases hl' <;>
    simp_all [berlin, city, gdr, germany, state, formerCountry, TimeInterval.Mem] <;> omega

/-- Hence every snapshot of the corrected fragment assigns at most one direct
class to each item. -/
theorem fragFixed_instAt_subsingleton (t : ℤ) (a : Qid) {c d : Qid}
    (hc : c ∈ fragFixed.instAt t a) (hd : d ∈ fragFixed.instAt t a) : c = d :=
  fragFixed.instAt_subsingleton fragFixed_functional t a hc hd

end TemporalExample

end Wikidata
