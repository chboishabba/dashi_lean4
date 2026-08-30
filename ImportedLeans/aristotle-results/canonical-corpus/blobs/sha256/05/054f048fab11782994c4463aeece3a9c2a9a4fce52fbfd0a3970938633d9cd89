import Synthesis.MonsterFibre
import AgdaMirror.MonsterWalk

/-!
# Synthesis layer 2': the walk state geometry and the two mask distances

`AgdaMirror.MonsterWalk` supplies a state carrier (`State = mask × window`), a
deterministic `step` driven by a measurement `Lens`, orbits, and a
first-difference "distance" `dMask` for which the supplied module *disproves*
the ultratriangle law.  `AgdaMirror.MonsterProjection15` supplies a different
mask distance, `len − lcpLen`, for which the ultratriangle law is *proved*.

The repository leaves the relation between the two unexplained.  It is proved
here:

* `firstDiff_eq_lcpLen` — the walk's `firstDiff` is exactly the
  longest-common-prefix length (on distinct masks);
* `walk_distance_complement` — on distinct length-15 masks the two quantities
  are complementary: `walkD x y + projD x y = 15`.  So the walk's `dMask` is a
  *closeness*, not a distance, which is precisely why the ultratriangle law
  fails for it and holds for its complement.  This turns the supplied negative
  result (`dMask_ultratriangle_false`) from an anomaly into a computed
  consequence.
* `step_mask_length` / `orbit_mask_length` — if every candidate mask has length
  15, the walk stays inside the length-15 mask carrier, hence inside the mask
  fibre of `Synthesis.MonsterFibre` and its transported ultrametric.  This is
  what licenses speaking of the walk as a trajectory in the Monster mask
  geometry at all.

Boundary: `State` is a list of booleans together with a natural number; "walk"
means iteration of the supplied `step`.  No spatial, physical, or continuum
interpretation is asserted.
-/

namespace Synthesis.WalkGeometry

open AgdaMirror.MonsterWalk (State Lens Candidates choose step orbit firstDiff)
open AgdaMirror.MonsterProjection15 (lcpLen lcpLen_le_left)

/-! ## The two mask quantities are complementary -/

/-- The walk's first-difference index is the longest-common-prefix length, for
any two distinct masks. -/
theorem firstDiff_eq_lcpLen :
    ∀ (x y : List Bool), x ≠ y → ∀ n, firstDiff x y n = n + lcpLen x y := by
  intro x
  induction x with
  | nil =>
    intro y hxy n
    cases y with
    | nil => exact absurd rfl hxy
    | cons c ys => cases c <;> simp [firstDiff, lcpLen]
  | cons b xs ih =>
    intro y hxy n
    cases y with
    | nil => cases b <;> simp [firstDiff, lcpLen]
    | cons c ys =>
      by_cases hbc : b = c
      · subst hbc
        have hne : xs ≠ ys := fun h => hxy (by rw [h])
        have := ih ys hne (n + 1)
        cases b <;> simp [firstDiff, lcpLen, this] <;> omega
      · cases b <;> cases c <;> simp_all [firstDiff, lcpLen]

/-- The walk's `dMask` is the common-prefix length of two distinct masks. -/
theorem walk_dMask_eq_lcpLen (x y : List Bool) (h : x ≠ y) :
    AgdaMirror.MonsterWalk.dMask x y = lcpLen x y := by
  simpa using firstDiff_eq_lcpLen x y h 0

/-- **The two supplied mask distances are complementary.**  On distinct length-15
masks, the walk quantity and the genuine ultrametric distance sum to 15: the
walk's `dMask` measures closeness, its complement measures distance. -/
theorem walk_distance_complement {x y : List Bool}
    (hx : x.length = 15) (hne : x ≠ y) :
    AgdaMirror.MonsterWalk.dMask x y + AgdaMirror.MonsterProjection15.dMask x y = 15 := by
  have h1 : AgdaMirror.MonsterWalk.dMask x y = lcpLen x y := walk_dMask_eq_lcpLen x y hne
  have h2 : lcpLen x y ≤ x.length := lcpLen_le_left x y
  simp only [h1, AgdaMirror.MonsterProjection15.dMask, hx] at *
  omega

/-- The genuine ultrametric distance is monotone-reversing in the walk
quantity: closer in the walk sense means smaller ultrametric distance. -/
theorem proj_lt_of_walk_gt {x z w : List Bool} {y : List Bool}
    (hx : x.length = 15) (hz : z.length = 15)
    (hxy : x ≠ y) (hzw : z ≠ w)
    (h : AgdaMirror.MonsterWalk.dMask z w < AgdaMirror.MonsterWalk.dMask x y) :
    AgdaMirror.MonsterProjection15.dMask x y < AgdaMirror.MonsterProjection15.dMask z w := by
  have h1 := walk_distance_complement hx hxy
  have h2 := walk_distance_complement hz hzw
  omega

/-! ## The walk stays inside the mask fibre -/

/-- If every candidate has length 15, so does the chosen mask. -/
theorem choose_length (L : Lens) (s : State) (cands : Candidates) (fallback : List Bool)
    (hc : ∀ m ∈ cands, m.length = 15) (hf : fallback.length = 15) :
    (choose L s cands fallback).length = 15 := by
  induction cands with
  | nil => exact hf
  | cons m ms ih =>
    by_cases h : L.admissible s m
    · simpa [choose, h] using hc m (by simp)
    · simp only [choose, h]
      exact ih (fun m' hm' => hc m' (by simp [hm']))

/-- One step keeps the walk inside the length-15 mask carrier. -/
theorem step_mask_length (L : Lens) (cands : Candidates) (s : State)
    (hc : ∀ m ∈ cands, m.length = 15) (hs : s.mask.length = 15) :
    (step L cands s).mask.length = 15 :=
  choose_length L s cands s.mask hc hs

/-- Hence every state of every orbit does. -/
theorem orbit_mask_length (L : Lens) (cands : Candidates)
    (hc : ∀ m ∈ cands, m.length = 15) :
    ∀ (n : Nat) (s : State), s.mask.length = 15 →
      ∀ t ∈ orbit L cands n s, t.mask.length = 15 := by
  intro n
  induction n with
  | zero =>
    intro s hs t ht
    simp only [orbit, List.mem_singleton] at ht
    subst ht; exact hs
  | succ n ih =>
    intro s hs t ht
    simp only [orbit, List.mem_cons] at ht
    rcases ht with rfl | ht
    · exact hs
    · exact ih (step L cands s) (step_mask_length L cands s hc hs) t ht

/-- The mask of a length-15 walk state, as an element of the Monster mask
geometry carrier. -/
def stateMask (s : State) (hs : s.mask.length = 15) :
    AgdaMirror.MonsterProjection15.Mask15 := ⟨s.mask, hs⟩

/-- **The walk is a trajectory in the Monster mask geometry.**  Under the
length-15 candidate discipline, consecutive states of an orbit have a
well-defined ultrametric distance, and that distance is the complement of the
supplied walk closeness whenever the step actually moves the mask. -/
theorem walk_step_distance (L : Lens) (cands : Candidates) (s : State)
    (hc : ∀ m ∈ cands, m.length = 15) (hs : s.mask.length = 15)
    (hmove : (step L cands s).mask ≠ s.mask) :
    AgdaMirror.MonsterProjection15.d15
        (stateMask (step L cands s) (step_mask_length L cands s hc hs)) (stateMask s hs)
      + AgdaMirror.MonsterWalk.dMask (step L cands s).mask s.mask = 15 := by
  have h := walk_distance_complement (step_mask_length L cands s hc hs) hmove
  simp only [stateMask, AgdaMirror.MonsterProjection15.d15]
  omega

end Synthesis.WalkGeometry
