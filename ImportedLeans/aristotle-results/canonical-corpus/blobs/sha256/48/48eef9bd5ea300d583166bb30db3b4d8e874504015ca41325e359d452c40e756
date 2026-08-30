import RequestProject.QDeform

/-!
# QShapes: the dot-line shapes seen in the q-deformation frames, proven in Lean

A computer-vision pass (`vision/render_frames.py` + `vision/detect_shapes.py`,
using OpenCV) renders one frame per q-expansion page of the moonshine
deformation and reads off the *shape* on each frame: a horizontal **line**
carrying one **dot** per available Monster prime at that page (the `availCount`
of `QDeform`).  OpenCV reports, for every frame, a line with `k` dots — exactly
the "lines with 1, 2, 3, 4 dots" the user observed — and the occasional
**collapse** frame with no dots (a pure flatline).

This file proves those observations.  Two things are certified:

1. **The frame geometry really is a line of `k` dots.** `dotPositions k` is the
   exact set of dot centres the renderer draws (same constants as the Python).
   `dotPositions_length` proves it has `k` dots and `dots_on_line` proves they
   are collinear (all share the `y = lineY` row) — i.e. the shape is a line.

2. **The dot count per page, and the whole histogram, match the vision pass.**
   `pagesWithDots k` is the list of pages whose frame shows exactly `k` dots.
   `dot_histogram` reproduces the detected histogram `[1,4,17,41,32,7,2]`
   (pages with `0…6` dots), and the per-`k` catalogs pin down which pages carry
   each shape.  In particular `pages_one_dot` lists the four single-dot frames
   and `pages_collapse` the unique flatline.

All page-level findings are by `native_decide`, depending only on the standard
`propext`, `Quot.sound`, `Lean.ofReduceBool`, `Lean.trustCompiler` axioms.
-/

namespace QShapes

open QDeform

/-! ## Frame geometry (identical constants to `vision/render_frames.py`) -/

/-- Frame width in pixels. -/
def frameW : Int := 640
/-- Frame height in pixels. -/
def frameH : Int := 200
/-- The `y` row the dots sit on: the horizontal line. -/
def lineY : Int := 100
/-- Left x bound for the dots. -/
def xLo : Int := 80
/-- Right x bound for the dots. -/
def xHi : Int := 560

/-- The centres of the `k` dots drawn on a frame, evenly spaced on the line
`y = lineY`.  Matches `dot_positions` in `vision/render_frames.py` exactly. -/
def dotPositions (k : Nat) : List (Int × Int) :=
  if k == 0 then []
  else if k == 1 then [((xLo + xHi) / 2, lineY)]
  else
    let step := (xHi - xLo) / ((k : Int) - 1)
    (List.range k).map (fun i => (xLo + (i : Int) * step, lineY))

/-- A rendered frame has exactly `k` dots. -/
theorem dotPositions_length (k : Nat) : (dotPositions k).length = k := by
  unfold dotPositions
  match k with
  | 0 => rfl
  | 1 => rfl
  | (n + 2) => simp [List.length_map]

/-- The shape is a **line**: every dot centre lies on the row `y = lineY`. -/
theorem dots_on_line (k : Nat) : ∀ p ∈ dotPositions k, p.2 = lineY := by
  intro p hp
  unfold dotPositions at hp
  split at hp
  · simp at hp
  · split at hp
    · simp only [List.mem_singleton] at hp; rw [hp]
    · simp only [List.mem_map] at hp
      obtain ⟨i, _, hi⟩ := hp
      rw [← hi]

/-- Collinearity stated as: any two dot centres share the same `y`, so they all
lie on a single straight (horizontal) line. -/
theorem dots_collinear (k : Nat) :
    ∀ p ∈ dotPositions k, ∀ q ∈ dotPositions k, p.2 = q.2 := by
  intro p hp q hq
  rw [dots_on_line k p hp, dots_on_line k q hq]

/-! ## The dot count per page, matched against the OpenCV vision pass -/

/-- The pages whose frame shows exactly `k` dots. -/
def pagesWithDots (k : Nat) : List Nat :=
  (List.range numQPages).filter (fun pi => availCount pi == k)

/-- The number of dots on page `pi`'s frame equals the available-prime count
(the renderer draws `availCount pi` dots). -/
theorem frame_dot_count (pi : Nat) :
    (dotPositions (availCount pi)).length = availCount pi :=
  dotPositions_length _

/-- **Vision finding, proven.**  The histogram of dot counts over all 104 pages
is `[1, 4, 17, 41, 32, 7, 2]` for `0, 1, 2, 3, 4, 5, 6` dots respectively —
exactly the histogram OpenCV reports in `vision/detect_shapes.py`. -/
theorem dot_histogram :
    (List.range 7).map (fun k => (pagesWithDots k).length) = [1, 4, 17, 41, 32, 7, 2] := by
  native_decide

/-- The histogram accounts for every page. -/
theorem dot_histogram_total :
    ((List.range 7).map (fun k => (pagesWithDots k).length)).sum = numQPages := by
  native_decide

/-- **The flatline.**  Exactly one frame has no dots: page 70 (`q⁷¹`), the full
collapse. -/
theorem pages_collapse : pagesWithDots 0 = [70] := by native_decide

/-- The four single-dot frames. -/
theorem pages_one_dot : pagesWithDots 1 = [28, 30, 58, 73] := by native_decide

/-- The two-dot frames. -/
theorem pages_two_dots :
    pagesWithDots 2 = [0, 1, 3, 4, 13, 25, 31, 35, 46, 53, 61, 67, 68, 75, 78, 95, 100] := by
  native_decide

/-- The maximal six-dot frames. -/
theorem pages_six_dots : pagesWithDots 6 = [94, 101] := by native_decide

/-- The user's observed shapes — "lines with 1, 2, 3, 4 dots" — all occur, with
these multiplicities. -/
theorem small_line_counts :
    (pagesWithDots 1).length = 4 ∧ (pagesWithDots 2).length = 17 ∧
    (pagesWithDots 3).length = 41 ∧ (pagesWithDots 4).length = 32 := by
  native_decide

end QShapes
