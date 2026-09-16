/-
# §4 / §7 of the BIDI note: the noncommutative telescope

This module proves, from scratch and with no placeholder, the two purely
algebraic/analytic facts the BIDI source side needs for a single differentiated
term:

* `norm_prod_before_sub_prod_after_le` — the ordered telescope estimate

      ‖A₁⋯Aₙ − B₁⋯Bₙ‖ ≤ Σₖ (∏_{j<k} bⱼ) · mₖ · (∏_{j>k} bⱼ)

  for factorwise data `‖Aᵢ‖ ≤ bᵢ`, `‖Bᵢ‖ ≤ bᵢ`, `‖Aᵢ − Bᵢ‖ ≤ mᵢ`.  It is
  obtained from the exact ordered identity
  `A₁⋯Aₙ − B₁⋯Bₙ = (A₁−B₁)A₂⋯Aₙ + B₁(A₂−B₂)A₃⋯Aₙ + ⋯`, which appears here as
  the induction step (a single application of the two-term splitting
  `a·P − b·Q = (a−b)·P + b·(P−Q)`).

* `teleBound_marked` — if exactly one stage `i⋆` is changed and every other
  stage carries defect `0`, the telescope bound collapses to the single product

      (∏_{j<i⋆} bⱼ) · m_{i⋆} · (∏_{j>i⋆} bⱼ).

`marked_product_bound` combines them: this is equation (22) of the note, valid
for an ordered product of *any* length, in particular for the literal four-stage
CMP109 derivative carrier `path → transport → dexp⁻¹/log → outer dexp`.

Everything is stated in an arbitrary normed ring with `‖1‖ = 1` (bounded
operators on a nonzero Hilbert space are such a ring), so it applies verbatim to
the operator factors of the Round72 algebra.
-/
import Mathlib

namespace RequestProject.YangMills.BIDI

variable {R : Type*} [NormedRing R]

/-- One stage of an ordered noncommutative product: the factor before the
replacement, the factor after it, an ordinary factor bound `bound` valid for
both, and a defect budget `defect` for their difference. -/
structure Stage (R : Type*) [NormedRing R] where
  /-- The factor occurring in the "before" product. -/
  before : R
  /-- The factor occurring in the "after" product. -/
  after : R
  /-- The ordinary (Gate4) factor bound, valid for both factors. -/
  bound : ℝ
  /-- The defect budget for the difference of the two factors. -/
  defect : ℝ

namespace Stage

/-- The factorwise hypotheses (10) of the note: both factors obey the same
ordinary bound, and their difference obeys the defect budget. -/
def Valid (s : Stage R) : Prop :=
  ‖s.before‖ ≤ s.bound ∧ ‖s.after‖ ≤ s.bound ∧ ‖s.before - s.after‖ ≤ s.defect

theorem Valid.bound_nonneg {s : Stage R} (h : s.Valid) : 0 ≤ s.bound :=
  le_trans (norm_nonneg _) h.1

theorem Valid.defect_nonneg {s : Stage R} (h : s.Valid) : 0 ≤ s.defect :=
  le_trans (norm_nonneg _) h.2.2

/-- The unchanged stage: `A = B`, ordinary bound `‖A‖`, defect `0`.  This is
law (19) of the note, `‖A − A‖ ≤ 0`, in usable form. -/
def unchanged (a : R) : Stage R where
  before := a
  after := a
  bound := ‖a‖
  defect := 0

theorem valid_unchanged (a : R) : (unchanged a : Stage R).Valid := by
  refine ⟨le_rfl, le_rfl, ?_⟩
  simp [unchanged]

end Stage

/-- The telescope majorant, defined by the recursion that the telescope identity
produces.  `teleBound_eq_sum` below identifies it with the displayed sum
`Σₖ (∏_{j<k} bⱼ)·mₖ·(∏_{j>k} bⱼ)`. -/
def teleBound : List (Stage R) → ℝ
  | [] => 0
  | s :: rest => s.defect * (rest.map Stage.bound).prod + s.bound * teleBound rest

@[simp] theorem teleBound_nil : teleBound ([] : List (Stage R)) = 0 := rfl

@[simp] theorem teleBound_cons (s : Stage R) (rest : List (Stage R)) :
    teleBound (s :: rest) =
      s.defect * (rest.map Stage.bound).prod + s.bound * teleBound rest := rfl

/-- The closed form of the telescope majorant: the sum over positions of
`(∏_{j<k} bⱼ)·mₖ·(∏_{j>k} bⱼ)`. -/
theorem teleBound_eq_sum (ss : List (Stage R)) :
    teleBound ss =
      ∑ k ∈ Finset.range ss.length,
        (((ss.map Stage.bound).take k).prod * ((ss.map Stage.defect).getD k 0) *
          (((ss.map Stage.bound).drop (k + 1)).prod)) := by
  induction ss with
  | nil => simp
  | cons s rest ih =>
      rw [teleBound_cons, ih, Finset.mul_sum, List.length_cons, Finset.sum_range_succ']
      simp only [List.map_cons, List.take_succ_cons, List.drop_succ_cons, List.prod_cons,
        List.take_zero, List.prod_nil, List.getD_cons_succ, List.getD_cons_zero,
        one_mul]
      rw [add_comm]
      congr 1
      refine Finset.sum_congr rfl fun k _ => by ring

/-- **The marked telescope**, equation (20)→(22) of the note: if every stage
except the single marked one is literally unchanged (defect `0`), the telescope
majorant collapses to one ordered product. -/
theorem teleBound_marked (pre : List (Stage R)) (s : Stage R) (post : List (Stage R))
    (hpre : ∀ t ∈ pre, t.defect = 0) (hpost : ∀ t ∈ post, t.defect = 0) :
    teleBound (pre ++ s :: post) =
      (pre.map Stage.bound).prod * s.defect * (post.map Stage.bound).prod := by
  induction pre with
  | nil =>
      have : teleBound post = 0 := by
        clear hpre
        induction post with
        | nil => simp
        | cons t rest ih =>
            have h0 : t.defect = 0 := hpost t (by simp)
            have hrest : ∀ u ∈ rest, u.defect = 0 := fun u hu => hpost u (by simp [hu])
            simp [h0, ih hrest]
      rw [List.nil_append, teleBound_cons, this, mul_zero, add_zero, List.map_nil,
        List.prod_nil, one_mul]
  | cons t pre ih =>
      have h0 : t.defect = 0 := hpre t (by simp)
      have hpre' : ∀ u ∈ pre, u.defect = 0 := fun u hu => hpre u (by simp [hu])
      rw [List.cons_append, teleBound_cons, h0, zero_mul, zero_add, ih hpre',
        List.map_cons, List.prod_cons]
      ring

section NormOne

variable [NormOneClass R]

/-- The ordinary product bound: `‖A₁⋯Aₙ‖ ≤ b₁⋯bₙ`. -/
theorem norm_prod_before_le (ss : List (Stage R)) (h : ∀ s ∈ ss, s.Valid) :
    ‖(ss.map Stage.before).prod‖ ≤ (ss.map Stage.bound).prod := by
  induction ss with
  | nil => simp
  | cons s rest ih =>
      have hs := h s (by simp)
      have hrest : ∀ t ∈ rest, t.Valid := fun t ht => h t (by simp [ht])
      have hprod : ‖(rest.map Stage.before).prod‖ ≤ (rest.map Stage.bound).prod := ih hrest
      simp only [List.map_cons, List.prod_cons]
      refine le_trans (norm_mul_le _ _) ?_
      exact mul_le_mul hs.1 hprod (norm_nonneg _) hs.bound_nonneg

theorem prod_bound_nonneg (ss : List (Stage R)) (h : ∀ s ∈ ss, s.Valid) :
    0 ≤ (ss.map Stage.bound).prod :=
  le_trans (norm_nonneg _) (norm_prod_before_le ss h)

/-- **The noncommutative telescope estimate**, equation (11) of the note.

For an ordered product of arbitrary length, factorwise ordinary bounds and
factorwise defect budgets give

  `‖A₁⋯Aₙ − B₁⋯Bₙ‖ ≤ Σₖ (∏_{j<k} bⱼ)·mₖ·(∏_{j>k} bⱼ)`.

The proof is the exact ordered identity (12), applied one factor at a time. -/
theorem norm_prod_before_sub_prod_after_le (ss : List (Stage R))
    (h : ∀ s ∈ ss, s.Valid) :
    ‖(ss.map Stage.before).prod - (ss.map Stage.after).prod‖ ≤ teleBound ss := by
  induction ss with
  | nil => simp
  | cons s rest ih =>
      have hs := h s (by simp)
      have hrest : ∀ t ∈ rest, t.Valid := fun t ht => h t (by simp [ht])
      have key : (s.before * (rest.map Stage.before).prod)
            - (s.after * (rest.map Stage.after).prod)
          = (s.before - s.after) * (rest.map Stage.before).prod
            + s.after * ((rest.map Stage.before).prod - (rest.map Stage.after).prod) := by
        noncomm_ring
      simp only [List.map_cons, List.prod_cons, teleBound_cons]
      rw [key]
      refine le_trans (norm_add_le _ _) ?_
      refine add_le_add ?_ ?_
      · refine le_trans (norm_mul_le _ _) ?_
        exact mul_le_mul hs.2.2 (norm_prod_before_le rest hrest) (norm_nonneg _)
          hs.defect_nonneg
      · refine le_trans (norm_mul_le _ _) ?_
        exact mul_le_mul hs.2.1 (ih hrest) (norm_nonneg _) hs.bound_nonneg

/-- **The marked product bound**: the complete statement (22).  One changed
stage with defect budget `m`, every other stage literally unchanged, and
ordinary bounds on all stages, give

  `‖Pᵇᵉᶠᵒʳᵉ − Pᵃᶠᵗᵉʳ‖ ≤ (∏_{j<i⋆} bⱼ)·m·(∏_{j>i⋆} bⱼ)`. -/
theorem marked_product_bound (pre : List (Stage R)) (s : Stage R) (post : List (Stage R))
    (hvalid : ∀ t ∈ pre ++ s :: post, t.Valid)
    (hpre : ∀ t ∈ pre, t.defect = 0) (hpost : ∀ t ∈ post, t.defect = 0) :
    ‖((pre ++ s :: post).map Stage.before).prod
        - ((pre ++ s :: post).map Stage.after).prod‖ ≤
      (pre.map Stage.bound).prod * s.defect * (post.map Stage.bound).prod := by
  have h := norm_prod_before_sub_prod_after_le (pre ++ s :: post) hvalid
  rwa [teleBound_marked pre s post hpre hpost] at h

/-! ## The literal four-stage CMP109 carrier

`path → transport → dexp⁻¹/log → outer dexp`, with the marked stage in each of
the four possible positions.  These are the four cases exhausted by R409. -/

section FourStage

variable (path transport logStage outer : Stage R)

/-- The ordered four-stage carrier (13), written outermost-first as in the
note's `A_out A_log A_tr A_path`. -/
def fourStage : List (Stage R) := [outer, logStage, transport, path]

theorem fourStage_bound_of_marked_outer
    (hvalid : ∀ t ∈ fourStage path transport logStage outer, t.Valid)
    (h1 : logStage.defect = 0) (h2 : transport.defect = 0) (h3 : path.defect = 0) :
    ‖((fourStage path transport logStage outer).map Stage.before).prod
        - ((fourStage path transport logStage outer).map Stage.after).prod‖ ≤
      outer.defect * (logStage.bound * (transport.bound * path.bound)) := by
  have h := marked_product_bound [] outer [logStage, transport, path]
    (by simpa [fourStage] using hvalid) (by simp)
    (by intro t ht; rcases List.mem_cons.1 ht with rfl | ht
        · exact h1
        rcases List.mem_cons.1 ht with rfl | ht
        · exact h2
        rcases List.mem_cons.1 ht with rfl | ht
        · exact h3
        simp at ht)
  simpa [fourStage] using h

theorem fourStage_bound_of_marked_log
    (hvalid : ∀ t ∈ fourStage path transport logStage outer, t.Valid)
    (h0 : outer.defect = 0) (h2 : transport.defect = 0) (h3 : path.defect = 0) :
    ‖((fourStage path transport logStage outer).map Stage.before).prod
        - ((fourStage path transport logStage outer).map Stage.after).prod‖ ≤
      outer.bound * logStage.defect * (transport.bound * path.bound) := by
  have h := marked_product_bound [outer] logStage [transport, path]
    (by simpa [fourStage] using hvalid)
    (by intro t ht; rcases List.mem_cons.1 ht with rfl | ht
        · exact h0
        simp at ht)
    (by intro t ht; rcases List.mem_cons.1 ht with rfl | ht
        · exact h2
        rcases List.mem_cons.1 ht with rfl | ht
        · exact h3
        simp at ht)
  simpa [fourStage, mul_assoc] using h

theorem fourStage_bound_of_marked_transport
    (hvalid : ∀ t ∈ fourStage path transport logStage outer, t.Valid)
    (h0 : outer.defect = 0) (h1 : logStage.defect = 0) (h3 : path.defect = 0) :
    ‖((fourStage path transport logStage outer).map Stage.before).prod
        - ((fourStage path transport logStage outer).map Stage.after).prod‖ ≤
      outer.bound * logStage.bound * transport.defect * path.bound := by
  have h := marked_product_bound [outer, logStage] transport [path]
    (by simpa [fourStage] using hvalid)
    (by intro t ht; rcases List.mem_cons.1 ht with rfl | ht
        · exact h0
        rcases List.mem_cons.1 ht with rfl | ht
        · exact h1
        simp at ht)
    (by intro t ht; rcases List.mem_cons.1 ht with rfl | ht
        · exact h3
        simp at ht)
  simpa [fourStage, mul_assoc] using h

theorem fourStage_bound_of_marked_path
    (hvalid : ∀ t ∈ fourStage path transport logStage outer, t.Valid)
    (h0 : outer.defect = 0) (h1 : logStage.defect = 0) (h2 : transport.defect = 0) :
    ‖((fourStage path transport logStage outer).map Stage.before).prod
        - ((fourStage path transport logStage outer).map Stage.after).prod‖ ≤
      outer.bound * logStage.bound * transport.bound * path.defect := by
  have h := marked_product_bound [outer, logStage, transport] path []
    (by simpa [fourStage] using hvalid)
    (by intro t ht; rcases List.mem_cons.1 ht with rfl | ht
        · exact h0
        rcases List.mem_cons.1 ht with rfl | ht
        · exact h1
        rcases List.mem_cons.1 ht with rfl | ht
        · exact h2
        simp at ht)
    (by simp)
  simpa [fourStage, mul_assoc] using h

end FourStage

end NormOne

end RequestProject.YangMills.BIDI
