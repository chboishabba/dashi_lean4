import RequestProject.Ternary.Balanced
import RequestProject.Epistemic.Quotient

/-!
# Two transverse observers of the three-block ternary carrier

The upstream tranche organises the `3 ^ 9` balanced-ternary states as three
blocks of three coordinates and reads them through two projections:

* **blockwise orientation** — forget, in each block independently, whether the
  block or its antipode was recorded;
* **aggregate** — add up all nine coordinate values.

It records that the two collide in *both* directions, that the blockwise
quotient has `14 ^ 3 = 2744` classes while the global antipodal quotient has
`9842`, and that a blockwise-orientation class of three non-central blocks has
eight states over it.

Here all of that is proved of the carrier:

* `Ternary.card_image_blockObs` — the blockwise observer takes exactly `2744`
  values, because its value set is the full product of three copies of the
  `14`-element class set of one block;
* `Ternary.two_mul_card_stateOrbits` — the *global* antipodal quotient has
  `9842` classes, so the two quotients are genuinely different
  (`blockwise_ne_global`);
* `Ternary.card_fibre_blockObs` — the fibre of the blockwise observer over a
  state is the product of its three block classes, hence `8` over a state whose
  blocks are all non-central (`card_fibre_blockObs_allPos`);
* `Ternary.aggregate_not_factorsThrough_blockObs` and
  `Ternary.blockObs_not_factorsThrough_aggregate` — neither observer is a
  function of the other, *for every* candidate decoding, since each has a
  collision the other separates;
* `Ternary.jointObs_universal` — and the pair of them is the least common
  refinement: any observer carrying both factors the pair.

The non-factorisation statements are instances of the project's existing
routing calculus (`Epistemic.FactorsThrough`, `Epistemic.not_factorsThrough`),
so the "transverse observers" of the source tranche are the same objects as the
epistemic layer's observers, not a parallel notion.
-/

namespace Ternary

open Finset

/-- One block: three balanced-ternary coordinates. -/
abbrev Block := Word 3

/-- A state of the three-block carrier: `27 ^ 3 = 3 ^ 9` states. -/
abbrev State := Fin 3 → Block

namespace State

/-- The aggregate of a state: the sum of all nine coordinate values. -/
def aggregate (f : State) : ℤ := ∑ j, Word.aggregate (f j)

/-- The global antipode: reverse every block. -/
def antipode (f : State) : State := fun j => Word.antipode (f j)

/-- The all-centre state. -/
def zero : State := fun _ => Word.zero 3

@[simp] theorem antipode_antipode (f : State) : antipode (antipode f) = f := by
  funext j
  simp [antipode]

theorem antipode_involutive : Function.Involutive antipode := antipode_antipode

theorem antipode_eq_self_iff (f : State) : antipode f = f ↔ f = zero := by
  constructor
  · intro h
    funext j
    exact (Word.antipode_eq_self_iff (f j)).1 (congrFun h j)
  · rintro rfl
    funext j
    exact (Word.antipode_eq_self_iff _).2 rfl

end State

/-- The carrier has `19683` states. -/
theorem card_state : Fintype.card State = 19683 := by
  have hpow : Fintype.card State = (Fintype.card Block) ^ 3 := by
    simp [State]
  rw [hpow, card_word]
  norm_num

/-! ## The blockwise orientation observer -/

-- @source DASHI Agda bridge (PR #582): blockwise orientation forgetting
/-- The orientation class of a single block. -/
def blockClass (b : Block) : Finset Block := pairOrbit Word.antipode b

-- @source DASHI Agda bridge (PR #582): the blockwise orientation observer
/-- The blockwise orientation observer: forget, in each block independently,
which of the block and its antipode was recorded. -/
def blockObs (f : State) : Fin 3 → Finset Block := fun j => blockClass (f j)

theorem blockObs_eq_iff (f g : State) :
    blockObs f = blockObs g ↔ ∀ j, f j ∈ blockClass (g j) := by
  constructor
  · intro h j
    have hj : blockClass (f j) = blockClass (g j) := congrFun h j
    have : f j ∈ blockClass (f j) := mem_pairOrbit_self _
    rwa [hj] at this
  · intro h
    funext j
    have hj := h j
    show blockClass (f j) = blockClass (g j)
    simp only [blockClass, pairOrbit, Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with hj | hj
    · rw [hj]
    · rw [hj]
      simp only [blockClass, pairOrbit, Word.antipode_antipode]
      exact Finset.pair_comm _ _

/-- **The blockwise observer takes exactly the product of block classes as
values.** -/
theorem image_blockObs :
    Finset.univ.image blockObs = Fintype.piFinset (fun _ : Fin 3 => orbits 3) := by
  ext g
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Fintype.mem_piFinset]
  constructor
  · rintro ⟨f, rfl⟩ j
    exact Finset.mem_image_of_mem _ (Finset.mem_univ (f j))
  · intro h
    choose b _ hb using fun j => Finset.mem_image.1 (h j)
    exact ⟨b, funext fun j => hb j⟩

/-- **The blockwise orientation quotient has `2744 = 14 ^ 3` classes.** -/
theorem card_image_blockObs : (Finset.univ.image blockObs).card = 2744 := by
  rw [image_blockObs, Fintype.card_piFinset]
  simp [card_orbits_three]

/-! ## The global antipodal quotient is a different quotient -/

/-- **The global antipodal quotient of the carrier has `9842` classes.** -/
theorem two_mul_card_stateOrbits :
    2 * (Finset.univ.image (pairOrbit State.antipode)).card = 19684 := by
  rw [two_mul_card_pairImage State.antipode State.antipode_involutive State.zero
    State.antipode_eq_self_iff, card_state]

theorem card_stateOrbits : (Finset.univ.image (pairOrbit State.antipode)).card = 9842 := by
  have := two_mul_card_stateOrbits
  omega

-- @source DASHI Agda bridge (PR #582): blockwise and global quotients differ
/-- Forgetting orientation block by block is not the same as forgetting it
globally. -/
theorem blockwise_ne_global :
    (Finset.univ.image blockObs).card ≠
      (Finset.univ.image (pairOrbit State.antipode)).card := by
  rw [card_image_blockObs, card_stateOrbits]
  decide

/-! ## Fibres of the blockwise observer -/

/-- **The fibre of the blockwise observer** over a state is the product of the
orientation classes of its blocks. -/
theorem card_fibre_blockObs (w : State) :
    (Finset.univ.filter (fun f : State => blockObs f = blockObs w)).card
      = ∏ j, (blockClass (w j)).card := by
  have hset : (Finset.univ.filter (fun f : State => blockObs f = blockObs w))
      = Fintype.piFinset (fun j => blockClass (w j)) := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    exact blockObs_eq_iff f w
  rw [hset, Fintype.card_piFinset]

/-- The all-positive state. -/
def allPos : State := fun _ _ => Trit.pos

/-- The state with the first block reversed. -/
def firstBlockFlipped : State := fun j => if j = 0 then (fun _ => Trit.neg) else (fun _ => Trit.pos)

/-- The all-centre state, as a state whose aggregate is zero for structural
reasons. -/
def structuralZero : State := State.zero

/-- A state whose aggregate is zero by cancellation rather than by being
central. -/
def cancellationZero : State :=
  fun j => if j = 0 then (fun i => if i = 0 then Trit.pos else if i = 1 then Trit.neg
    else Trit.zer) else fun _ => Trit.zer

-- @source DASHI Agda bridge (PR #582): eight states over one non-central class
/-- **Eight states lie over the blockwise class of a state with three
non-central blocks.** -/
theorem card_fibre_blockObs_allPos :
    (Finset.univ.filter (fun f : State => blockObs f = blockObs allPos)).card = 8 := by
  rw [card_fibre_blockObs]
  have hj : ∀ j : Fin 3, (blockClass (allPos j)).card = 2 := by
    intro j
    refine Finset.card_pair ?_
    intro h
    have := congrFun h (0 : Fin 3)
    simp [allPos, Word.antipode, Trit.antipode] at this
  simp [hj]

/-! ## The two observers are transverse -/

theorem blockObs_allPos_eq_firstBlockFlipped : blockObs allPos = blockObs firstBlockFlipped := by
  rw [blockObs_eq_iff]
  intro j
  by_cases h : j = 0
  · subst h
    have : firstBlockFlipped 0 = fun _ => Trit.neg := by simp [firstBlockFlipped]
    rw [this]
    simp only [blockClass, pairOrbit, Finset.mem_insert, Finset.mem_singleton]
    right
    funext i
    rfl
  · have : firstBlockFlipped j = fun _ => Trit.pos := by simp [firstBlockFlipped, h]
    rw [this]
    exact mem_pairOrbit_self _

theorem aggregate_allPos : State.aggregate allPos = 9 := by
  simp [State.aggregate, Word.aggregate, allPos, Trit.val]

theorem aggregate_firstBlockFlipped : State.aggregate firstBlockFlipped = 3 := by
  simp [State.aggregate, Word.aggregate, firstBlockFlipped, Trit.val, Fin.sum_univ_succ]

theorem aggregate_structuralZero : State.aggregate structuralZero = 0 := by
  simp [State.aggregate, Word.aggregate, structuralZero, State.zero, Word.zero, Trit.val]

theorem aggregate_cancellationZero : State.aggregate cancellationZero = 0 := by
  simp [State.aggregate, Word.aggregate, cancellationZero, Trit.val, Fin.sum_univ_succ]

theorem blockObs_structuralZero_ne_cancellationZero :
    blockObs structuralZero ≠ blockObs cancellationZero := by
  intro h
  have h0 := (blockObs_eq_iff _ _).1 h 0
  simp only [blockClass, pairOrbit, Finset.mem_insert, Finset.mem_singleton] at h0
  rcases h0 with h0 | h0
  · have := congrFun h0 (0 : Fin 3)
    simp [structuralZero, State.zero, Word.zero, cancellationZero] at this
  · have := congrFun h0 (0 : Fin 3)
    simp [structuralZero, State.zero, Word.zero, cancellationZero, Word.antipode,
      Trit.antipode] at this

-- @source DASHI Agda bridge (PR #582): aggregate does not factor through block orientation
/-- **The aggregate is not a function of the blockwise orientation class** — for
*every* candidate decoding, because the two observers collide differently. -/
theorem aggregate_not_factorsThrough_blockObs :
    ¬ Epistemic.FactorsThrough blockObs State.aggregate := by
  refine Epistemic.not_factorsThrough blockObs_allPos_eq_firstBlockFlipped ?_
  rw [aggregate_allPos, aggregate_firstBlockFlipped]
  decide

-- @source DASHI Agda bridge (PR #582): block orientation does not factor through the aggregate
/-- **The blockwise orientation class is not a function of the aggregate.** -/
theorem blockObs_not_factorsThrough_aggregate :
    ¬ Epistemic.FactorsThrough State.aggregate blockObs := by
  refine Epistemic.not_factorsThrough ?_ blockObs_structuralZero_ne_cancellationZero
  rw [aggregate_structuralZero, aggregate_cancellationZero]

/-! ## The joint observer -/

-- @source DASHI Agda bridge (PR #582): the joint observer of the two projections
/-- The joint observer: record both coordinates. -/
def jointObs (f : State) : (Fin 3 → Finset Block) × ℤ := (blockObs f, State.aggregate f)

theorem jointObs_carries_blockObs : Epistemic.FactorsThrough jointObs blockObs :=
  ⟨Prod.fst, fun _ => rfl⟩

theorem jointObs_carries_aggregate : Epistemic.FactorsThrough jointObs State.aggregate :=
  ⟨Prod.snd, fun _ => rfl⟩

-- @source DASHI Agda bridge (PR #582): any common observer carrying both factors the joint
/-- **The joint observer is the least common refinement**: any observer through
which both projections factor also carries the joint observer. -/
theorem jointObs_universal {Common : Type} (common : State → Common)
    (hblock : Epistemic.FactorsThrough common blockObs)
    (hagg : Epistemic.FactorsThrough common State.aggregate) :
    Epistemic.FactorsThrough common jointObs := by
  obtain ⟨decodeBlock, hb⟩ := hblock
  obtain ⟨decodeAgg, ha⟩ := hagg
  exact ⟨fun c => (decodeBlock c, decodeAgg c), fun f => by
    simp [jointObs, hb f, ha f]⟩

/-- Two blocks of opposite sign, the third central. -/
def twin : State := fun j => if j = 0 then (fun _ => Trit.pos)
  else if j = 1 then (fun _ => Trit.neg) else fun _ => Trit.zer

/-- The same two blocks with both orientations reversed. -/
def twinFlipped : State := State.antipode twin

/-- The joint observer is still not world-complete: reversing two blocks of
opposite sign changes neither the blockwise classes nor the aggregate. -/
theorem jointObs_not_injective : ¬ Function.Injective jointObs := by
  intro hinj
  have hblock : blockObs twin = blockObs twinFlipped := by
    rw [blockObs_eq_iff]
    intro j
    have hflip : Word.antipode (twinFlipped j) = twin j := by
      simp [twinFlipped, State.antipode]
    simp only [blockClass, pairOrbit, Finset.mem_insert, Finset.mem_singleton]
    exact Or.inr hflip.symm
  have hagg : State.aggregate twin = State.aggregate twinFlipped := by
    simp [State.aggregate, twinFlipped, State.antipode, twin, Word.aggregate, Word.antipode,
      Trit.val, Trit.antipode, Fin.sum_univ_succ]
  have hne : twin ≠ twinFlipped := by
    intro h
    have h0 := congrFun (congrFun h 0) 0
    simp [twin, twinFlipped, State.antipode, Word.antipode, Trit.antipode] at h0
  exact hne (hinj (by simp [jointObs, hblock, hagg]))

end Ternary
