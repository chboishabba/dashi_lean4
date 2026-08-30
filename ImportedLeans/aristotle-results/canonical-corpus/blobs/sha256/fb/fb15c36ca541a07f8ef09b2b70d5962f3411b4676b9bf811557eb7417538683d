import RequestProject.Irrep170

/-!
# OpenCVShapes: a formal theory of the shapes the OpenCV pass detected

This file formalizes the only *checkable* mathematical content of the long
visualization thread: the OpenCV log that recorded, for each "page" `n` of the
Moonshine animation, how many dots (`detected_dots`) the computer-vision pass
found, together with the observation that on exactly one page the cluster
collapses to **0 dots** (a "flatline").

The log was pasted as a single un-delimited blob.  Its rows have the schema

```
page_index, detected_dots, lean_dots, collinear, shape, match
```

with `match = 1` on every row (the vision count always agreed with the
recorded `lean_dots`).  The recorded pages run `0, 1, …, 103`.

## The central correction: the collapse is at page 70, not 170

The thread fixated on the claim that the collapse happens at page **170**, and
then read deep meaning into `170` being the number of *distinct* Monster
irreducible-representation degrees (`Irrep170.monsterIrrepDegrees_distinct`).

That "170" is a **parsing artifact**, not a page index.  Every row ends in the
`match` field, whose value is always `1`.  When the newline between two rows is
removed (as happens when the CSV is pasted as one blob), the trailing `1` of one
row fuses with the page index of the next:

```
… ,line with 5 dots,1   ⟶  … ,line with 5 dots,1
70,0,0,1,collapse…           70,0,0,1,collapse…
```

becomes the contiguous string `… ,line with 5 dots,170,0,0,1,collapse…`.

So `"1" ++ "70" = "170"`: the genuine collapse page is **70**
(`openCVCollapseString` records this fusion).  The recorded data does not even
contain a page `170` — only pages `0 … 103` were logged.

## What this file proves

* `openCVDots_length` — exactly 104 pages (`0 … 103`) were recorded.
* `openCVDots_collapse_at_70` — page 70 has `0` detected dots.
* `openCVDots_unique_collapse` — page 70 is the **only** page whose dot count is
  `0`; this is the unique flatline.
* `openCVDots_no_page_170` — there is no page `170` in the recorded data, so the
  "collapse at 170" reading is impossible on the data itself.
* `openCVCollapseString` — the string identity `"1" ++ "70" = "170"` that
  explains the misread.
* `collapsePage_ne_numDistinctIrreps` — the genuine collapse page `70` is *not*
  equal to the number `170` of distinct Monster irrep degrees, so the alleged
  "smoking-gun coincidence" conflates two different numbers.

## On the rest of the thread (honest scope statement)

The number `170 = ` distinct Monster irrep degrees is a real number-theoretic
invariant, proved with no `sorry` in `Irrep170.lean`.  It stands on its own.
It is **not** linked to the animation: the animation's only collapse is at page
`70`.  The dot counts themselves are raw OpenCV detections; they are *not*
reproduced by the natural number-theoretic rule "number of distinct Monster
primes dividing the corresponding degree" (that rule gives the sequence
`0, 3, 5, 6, 8, …`, which disagrees with the recorded `2, 2, 3, 2, 2, …` from the
very first pages).  The elaborate narrative around an "M = 4 deformation",
"kernel collapse", "Euler characteristic 0", and "deriving 80% of Mathlib from
the Monster" is informal speculation and is *not* formalized here, because none
of it is mathematically well-founded.
-/

namespace OpenCVShapes

/-- The `detected_dots` column of the OpenCV log, indexed by page `0 … 103`.
This is the genuine, de-merged reading of the pasted CSV blob. -/
def openCVDots : List Nat :=
[
  2, 2, 3, 2, 2, 4, 3, 3, 3, 4,        -- pages 0–9
  4, 3, 4, 2, 3, 3, 3, 3, 3, 3,        -- pages 10–19
  3, 5, 3, 5, 3, 2, 4, 5, 1, 4,        -- pages 20–29
  1, 2, 4, 3, 4, 2, 4, 3, 3, 4,        -- pages 30–39
  3, 4, 3, 4, 4, 3, 2, 3, 3, 4,        -- pages 40–49
  4, 4, 3, 2, 3, 3, 4, 4, 1, 4,        -- pages 50–59
  3, 2, 4, 4, 4, 4, 3, 2, 2, 5,        -- pages 60–69
  0, 3, 5, 1, 3, 2, 4, 4, 2, 3,        -- pages 70–79  (page 70 = collapse)
  3, 3, 3, 4, 4, 3, 4, 4, 3, 3,        -- pages 80–89
  4, 3, 5, 3, 6, 2, 3, 5, 3, 3,        -- pages 90–99
  2, 6, 4, 4                            -- pages 100–103
]

/-- The page index at which the animation collapses (0 detected dots). -/
def collapsePage : Nat := 70

/-- Exactly 104 pages (`0 … 103`) were recorded. -/
theorem openCVDots_length : openCVDots.length = 104 := by native_decide

/-- Page 70 has `0` detected dots: this is the recorded flatline. -/
theorem openCVDots_collapse_at_70 : openCVDots.getD collapsePage 1 = 0 := by
  native_decide

/-- **The collapse is unique.**  Page 70 is the only recorded page whose dot
count is `0`. -/
theorem openCVDots_unique_collapse :
    (List.range openCVDots.length).filter (fun n => openCVDots.getD n 1 = 0)
      = [collapsePage] := by
  native_decide

/-- Every page other than the collapse page has at least one detected dot. -/
theorem openCVDots_pos_off_collapse (n : Nat) (hn : n < openCVDots.length)
    (hne : n ≠ collapsePage) : 0 < openCVDots.getD n 1 := by
  have h := openCVDots_unique_collapse
  by_contra hle
  have h0 : openCVDots.getD n 1 = 0 := Nat.le_zero.1 (Nat.not_lt.1 hle)
  have hmem : n ∈ (List.range openCVDots.length).filter (fun m => openCVDots.getD m 1 = 0) := by
    rw [List.mem_filter, List.mem_range]
    exact ⟨hn, decide_eq_true h0⟩
  rw [h] at hmem
  simp at hmem
  exact hne hmem

/-- The recorded data has **no page 170**: only pages `0 … 103` exist, so a
"collapse at page 170" cannot be read off the data. -/
theorem openCVDots_no_page_170 : ¬ (170 < openCVDots.length) := by native_decide

/-- **The parsing artifact.**  The misread "170" is the fusion of the `match`
column `1` of the preceding row with the genuine page index `70`:
`"1" ++ "70" = "170"`. -/
theorem openCVCollapseString : toString 1 ++ toString collapsePage = "170" := by
  native_decide

/-- The genuine collapse page (`70`) is not the number of distinct Monster
irrep degrees (`170`): the celebrated "coincidence" conflated two different
numbers. -/
theorem collapsePage_ne_numDistinctIrreps :
    collapsePage ≠ Irrep170.monsterIrrepDegrees.eraseDups.length := by
  native_decide

/-- For the record: the genuine number-theoretic invariant referenced in the
thread (the number of *distinct* Monster irrep degrees) is `170`.  This is a
real fact about the Monster, established independently in `Irrep170.lean`; it is
unrelated to the animation, whose only collapse is at page `70`. -/
theorem numDistinctIrreps_eq_170 :
    Irrep170.monsterIrrepDegrees.eraseDups.length = 170 := by native_decide

end OpenCVShapes
