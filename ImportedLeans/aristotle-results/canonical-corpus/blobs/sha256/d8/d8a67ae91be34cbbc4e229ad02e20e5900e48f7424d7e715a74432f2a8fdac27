import RequestProject.ProgramAlgebra

/-!
# Signed programs: inverses, and the integer grading

`RequestProject.ProgramAlgebra` grades the *forward* words in `subclass of` and
`instance of` by a natural number, the count of `instance of` letters.  Allowing
each letter to be run **backwards** — the `^wdt:P31` of a property path — turns
that grading into an honest integer one: a backwards `instance of` step lowers
the metaclass level by one.

* `SLink`, `sdegree` — signed letters and the integer degree of a signed word,
  additive along concatenation (`sdegree_append`);
* `swordExpr` — a signed word *is* a property path, built from atoms and
  inverses, so the semantics of `RequestProject.Paths` applies unchanged;
* `Ontology.level_add_sdegree` — **the degree is the level displacement**, now
  with cancellation: a forward and a backward `instance of` step cancel;
* `Ontology.sdegree_eq_zero_of_closed` — a closed signed walk has degree zero,
  and `KB.no_ontology_of_sword_return` turns any closing signed word of non-zero
  degree in a knowledge base into a proof that no ontology models it;
* `KB.roundTrip_isReturn` — the reason the search of
  `RequestProject.SpectrumReport` uses forward words only: with inverses allowed
  every statement closes a word, since `x ⊑ y` and back is a loop.  What
  survives as an invariant is not the existence of a loop but its degree.
-/

namespace Wikidata

/-- A letter of the signed alphabet: one of the two relations, to be run
forwards or backwards. -/
structure SLink where
  /-- The relation. -/
  link : Link
  /-- Whether it is run forwards. -/
  fwd : Bool
deriving DecidableEq, Repr, Inhabited

namespace SLink

/-- The metaclass level shift of a signed letter: `instance of` raises the level
by one, its inverse lowers it, `subclass of` keeps it either way. -/
def degree (s : SLink) : ℤ :=
  match s.link with
  | .p31 => if s.fwd then 1 else -1
  | .p279 => 0

end SLink

/-- The degree of a signed word: the sum of the degrees of its letters. -/
def sdegree (w : List SLink) : ℤ := (w.map SLink.degree).sum

@[simp] theorem sdegree_nil : sdegree [] = 0 := rfl

@[simp] theorem sdegree_cons (s : SLink) (w : List SLink) :
    sdegree (s :: w) = s.degree + sdegree w := by
  simp [sdegree]

/-- **The degree is a homomorphism** from signed words under concatenation to the
integers under addition. -/
theorem sdegree_append (v w : List SLink) : sdegree (v ++ w) = sdegree v + sdegree w := by
  induction v with
  | nil => simp
  | cons s v ih => simp [ih]; ring

/-- A signed word, read as a property path: atoms for the forward letters,
inverses of atoms for the backward ones. -/
def swordExpr (w : List SLink) : PathExpr Link :=
  w.foldr (fun s e => .seq (if s.fwd then .atom s.link else .inv (.atom s.link)) e) .id

@[simp] theorem swordExpr_nil : swordExpr [] = .id := rfl

@[simp] theorem swordExpr_cons (s : SLink) (w : List SLink) :
    swordExpr (s :: w) =
      .seq (if s.fwd then .atom s.link else .inv (.atom s.link)) (swordExpr w) := rfl

namespace Ontology

variable {I : Type*} {O : Ontology I}

/-- One signed step moves the metaclass level by the degree of its letter. -/
theorem level_step : ∀ (s : SLink) {x m : I},
    PathExpr.Eval O.linkRel
        (if s.fwd then PathExpr.atom s.link else PathExpr.inv (PathExpr.atom s.link)) x m →
      (O.level m : ℤ) = (O.level x : ℤ) + s.degree := by
  rintro ⟨l, b⟩ x m h
  cases b with
  | false =>
      cases l with
      | p31 =>
          have h31 : O.P31 m x := h
          have hlev : (O.level x : ℤ) = (O.level m : ℤ) + 1 := by
            exact_mod_cast O.level_P31 h31
          show (O.level m : ℤ) = (O.level x : ℤ) + (-1 : ℤ)
          omega
      | p279 =>
          have h279 : O.P279 m x := h
          have hlev : (O.level m : ℤ) = (O.level x : ℤ) := by
            exact_mod_cast O.level_P279 h279
          show (O.level m : ℤ) = (O.level x : ℤ) + (0 : ℤ)
          omega
  | true =>
      cases l with
      | p31 =>
          have h31 : O.P31 x m := h
          have hlev : (O.level m : ℤ) = (O.level x : ℤ) + 1 := by
            exact_mod_cast O.level_P31 h31
          show (O.level m : ℤ) = (O.level x : ℤ) + (1 : ℤ)
          omega
      | p279 =>
          have h279 : O.P279 x m := h
          have hlev : (O.level x : ℤ) = (O.level m : ℤ) := by
            exact_mod_cast O.level_P279 h279
          show (O.level m : ℤ) = (O.level x : ℤ) + (0 : ℤ)
          omega

/-- **Along a signed word the metaclass level moves by the degree of the word**:
forward `instance of` steps raise it, backward ones lower it, and `subclass of`
steps in either direction keep it. -/
theorem level_add_sdegree :
    ∀ (w : List SLink) {x y : I}, PathExpr.Eval O.linkRel (swordExpr w) x y →
      (O.level y : ℤ) = (O.level x : ℤ) + sdegree w := by
  intro w
  induction w with
  | nil =>
      intro x y h
      have hxy : x = y := h
      simp [← hxy]
  | cons s w ih =>
      intro x y h
      rw [swordExpr_cons] at h
      obtain ⟨m, hm, hrest⟩ := h
      have hstep := ih hrest
      have hlevel := level_step s hm
      rw [hstep, hlevel, sdegree_cons]
      ring

/-- **A closed signed walk has degree zero.** -/
theorem sdegree_eq_zero_of_closed {w : List SLink} {x : I}
    (h : PathExpr.Eval O.linkRel (swordExpr w) x x) : sdegree w = 0 := by
  have := level_add_sdegree w h
  omega

end Ontology

namespace KB

variable (kb : KB)

/-- The items that are direct instances of a class: the reverse of the
`instance of` step. -/
def directInstancesL (c : Qid) : List Qid := (kb.inst.filter (fun p => p.2 == c)).map Prod.fst

variable {kb}

theorem mem_directInstancesL {a c : Qid} : a ∈ kb.directInstancesL c ↔ kb.Inst a c := by
  simp only [directInstancesL, List.mem_map, List.mem_filter, beq_iff_eq, Inst]
  constructor
  · rintro ⟨⟨u, v⟩, ⟨hmem, hv⟩, hu⟩
    cases hu; cases hv; exact hmem
  · intro h; exact ⟨(a, c), ⟨h, rfl⟩, rfl⟩

variable (kb)

/-- The one-step operator of a signed letter. -/
def slinkStepL : SLink → Qid → List Qid := fun s q =>
  if s.fwd then kb.linkStepL s.link q
  else match s.link with
    | .p279 => kb.subsL q
    | .p31 => kb.directInstancesL q

/-- **The operator of a signed word**: apply its letters from left to right. -/
def swordStep (kb : KB) : List SLink → Qid → List Qid
  | [], q => [q]
  | s :: w, q => ((kb.slinkStepL s q).flatMap (swordStep kb w)).dedup

variable {kb}

theorem mem_slinkStepL {s : SLink} {a b : Qid} :
    b ∈ kb.slinkStepL s a ↔
      (if s.fwd then kb.LinkRel s.link a b else kb.LinkRel s.link b a) := by
  rcases hb : s.fwd with _ | _
  · cases hs : s.link with
    | p31 => simp [slinkStepL, hb, hs, LinkRel, mem_directInstancesL]
    | p279 => simp [slinkStepL, hb, hs, LinkRel, mem_subsL]
  · simp [slinkStepL, hb, mem_linkStepL]

/-- **The operator computes the path semantics of the signed word.** -/
theorem mem_swordStep :
    ∀ (w : List SLink) {x y : Qid},
      y ∈ kb.swordStep w x ↔ PathExpr.Eval kb.LinkRel (swordExpr w) x y := by
  intro w
  induction w with
  | nil => intro x y; simp [swordStep, eq_comm]
  | cons s w ih =>
      intro x y
      simp only [swordStep, List.mem_dedup, List.mem_flatMap, swordExpr_cons]
      constructor
      · rintro ⟨m, hm, hy⟩
        refine ⟨m, ?_, ih.1 hy⟩
        rcases hb : s.fwd with _ | _ <;>
          simpa [hb, PathExpr.Eval] using (mem_slinkStepL (s := s)).1 hm
      · rintro ⟨m, hm, hy⟩
        refine ⟨m, ?_, ih.2 hy⟩
        refine (mem_slinkStepL (s := s)).2 ?_
        rcases hb : s.fwd with _ | _ <;> simpa [hb, PathExpr.Eval] using hm

/-- **A closing signed word of non-zero degree rules out every ontology.** -/
theorem no_ontology_of_sword_return {w : List SLink} {x : Qid}
    (hper : Periodicity.IsPeriodic (kb.swordStep w) x) (hw : sdegree w ≠ 0)
    (O : Ontology Qid) (hO : O.linkRel = kb.LinkRel) : False := by
  obtain ⟨n, hn, hreach⟩ := hper
  have key : ∀ m (y : Qid), Periodicity.ReachIn (kb.swordStep w) m x y →
      (O.level y : ℤ) = (O.level x : ℤ) + m * sdegree w := by
    intro m
    induction m with
    | zero =>
        intro y hy
        rw [← Periodicity.reachIn_zero_iff.1 hy]
        simp
    | succ m ih =>
        intro z hz
        obtain ⟨y, hy, hstep⟩ := Periodicity.reachIn_succ_iff.1 hz
        have h1 := ih y hy
        have h2 : (O.level z : ℤ) = (O.level y : ℤ) + sdegree w := by
          refine Ontology.level_add_sdegree w ?_
          rw [hO]
          exact (mem_swordStep w).1 hstep
        rw [h2, h1]
        push_cast
        ring
  have hx := key n x hreach
  have hzero : (n : ℤ) * sdegree w = 0 := by omega
  have hnne : n ≠ 0 := by omega
  have hn0 : (n : ℤ) ≠ 0 := by exact_mod_cast hnne
  rcases mul_eq_zero.1 hzero with h | h
  · exact hn0 h
  · exact hw h

/-- **With inverses allowed every statement closes a word**: one `subclass of`
step forward and the same step back is a loop, of degree zero.  This is why the
periodicity search runs over forward words: for signed words the informative
invariant is the degree, not the existence of a loop. -/
theorem roundTrip_isReturn {a b : Qid} (h : kb.Sub a b) :
    Periodicity.IsReturn (kb.swordStep [⟨.p279, true⟩, ⟨.p279, false⟩]) 1 a := by
  refine ⟨Nat.one_pos, Periodicity.reachIn_one_iff.2 ?_⟩
  refine (mem_swordStep _).2 ?_
  exact ⟨b, h, a, h, rfl⟩

/-- … and that loop has degree zero, as every closed walk must. -/
theorem roundTrip_sdegree : sdegree [⟨Link.p279, true⟩, ⟨Link.p279, false⟩] = 0 := by
  decide

end KB

end Wikidata
