import RequestProject.DualAtlas

/-!
# VisionPatterns — Lean certification of the OpenCV pattern findings

The vision pipeline (`vision/atlas/render_views.py` + `vision/atlas/detect_patterns.py`)
rendered the dual-atlas projection rasters emitted by `RequestProject.VisionAtlas`
for all four corpora (**itself / mathlib / batteries / lean4**), looked for
structure with OpenCV, swept the detector parameters, and compared every module
against every other across the `cog`, `triad`, and `harm` views.

This file freezes the **reproducible** findings as literal data and certifies
them.  The literals below are exactly the histogram rows written to
`vision/atlas/*_{cog,triad,harm}.csv` and consumed by the OpenCV stage, so a
theorem here is a machine-checked statement about the very pixels OpenCV saw.

The patterns proved:

* **Harmonic dominance (cross-module).** In *every* corpus the trivector cell
  (harmonic code `0`) is the strict, unique maximum of the harmonic histogram
  (`*_harm_trivector_dominant`, `harm_trivector_dominant_all`).
* **Harmonic monotonicity (large corpora).** For the three large corpora the
  whole harmonic histogram is *strictly decreasing* in code order
  `0 > 5 > 7 > 11 > 13` (`*_harm_strictDecreasing`,
  `harm_strictDecreasing_large`).  The small `itself` corpus is the lone
  exception, also certified (`itself_harm_not_decreasing`).
* **Argmax buckets (per view).** The OpenCV `argmax` of each `cog` and `triad`
  raster, certified as the unique maximum bucket (`*_cog_argmax`,
  `*_triad_argmax`).
* **Range soundness.** Every datapoint feeding these rasters is in range, by the
  projection guarantees `DualAtlas.cogProj_mem` and `DualAtlas.triadProj_le`
  (re-exported as `cog_in_range`, `triad_in_range`).

All data-level proofs are by `native_decide`; the range lemmas are the abstract
`DualAtlas` theorems.
-/

namespace VisionPatterns

/-! ## §1  The raster literals (verbatim from `vision/atlas/*.csv`) -/

/-- `cog` histogram (92 buckets, indices `0..91` ↔ `cog = 1..92`) — corpus `itself`. -/
def itselfCog : List Nat :=
  [4, 7, 3, 1, 4, 2, 3, 4, 2, 2, 3, 1, 1, 4, 4, 2, 1, 5, 3, 1, 3, 4, 2, 1, 3, 4, 1, 2, 6, 2, 4, 0, 1, 1, 7, 5, 5, 5, 5, 4, 1, 3, 1, 5, 3, 0, 2, 0, 1, 1, 1, 7, 2, 4, 5, 1, 5, 0, 4, 2, 4, 8, 2, 7, 3, 5, 3, 2, 3, 1, 4, 4, 4, 4, 3, 1, 2, 10, 2, 4, 5, 4, 5, 5, 3, 4, 3, 2, 3, 5, 4, 4]
/-- `cog` histogram — corpus `mathlib`. -/
def mathlibCog : List Nat :=
  [5465, 5321, 5274, 5289, 5160, 5819, 5441, 5436, 5659, 5756, 6064, 5960, 5510, 5534, 5278, 5379, 5618, 5124, 5356, 5380, 5086, 5369, 5338, 5313, 5267, 5648, 5286, 5423, 5356, 5222, 5619, 5634, 5705, 5456, 5508, 5408, 5549, 5729, 5612, 5836, 5509, 5453, 5427, 5580, 5429, 5905, 5747, 6387, 5729, 6129, 5350, 5484, 5183, 5332, 5259, 5709, 5487, 5802, 5227, 5244, 5679, 5525, 5348, 5235, 5524, 5248, 5542, 5556, 5513, 5329, 5195, 5783, 5657, 5387, 5718, 5326, 5207, 5194, 5585, 5308, 5244, 5650, 5198, 5376, 5320, 5563, 5783, 5328, 5640, 5571, 5390, 5238]
/-- `cog` histogram — corpus `batteries`. -/
def batteriesCog : List Nat :=
  [99, 127, 116, 103, 95, 114, 112, 99, 94, 107, 98, 89, 104, 138, 94, 101, 132, 91, 112, 85, 98, 101, 108, 118, 87, 94, 108, 102, 127, 106, 106, 105, 112, 77, 138, 106, 81, 107, 101, 102, 107, 112, 96, 93, 106, 73, 97, 104, 90, 75, 97, 106, 109, 105, 112, 149, 108, 103, 101, 104, 118, 99, 102, 110, 104, 90, 111, 101, 88, 101, 82, 110, 110, 102, 130, 109, 109, 102, 96, 94, 120, 122, 121, 99, 87, 95, 96, 100, 123, 124, 93, 113]
/-- `cog` histogram — corpus `lean4`. -/
def lean4Cog : List Nat :=
  [1907, 1844, 1930, 1860, 1862, 1978, 1780, 1966, 2440, 1931, 1912, 1919, 1882, 1836, 2006, 1897, 2504, 1839, 1942, 1879, 1844, 1964, 1912, 2089, 1902, 1980, 1869, 2051, 1888, 2048, 1866, 1930, 1829, 2063, 3638, 1917, 1864, 1889, 1989, 1883, 2826, 1799, 1983, 1900, 2884, 1870, 1972, 1945, 1870, 2029, 1898, 2020, 1819, 1864, 2023, 1942, 1981, 1922, 1798, 1823, 1934, 1950, 1938, 1936, 2179, 1881, 2042, 1947, 1946, 1961, 2022, 2000, 1933, 1882, 2005, 1932, 2100, 1965, 1908, 1921, 2011, 2012, 1871, 2331, 2039, 1988, 1933, 1850, 1827, 2840, 2025, 2072]

/-- `triad` histogram (20 buckets, indices `0..19`) — corpus `itself`. -/
def itselfTriad : List Nat :=
  [12, 11, 17, 18, 16, 12, 10, 20, 18, 20, 13, 15, 12, 21, 13, 15, 17, 7, 9, 17]
/-- `triad` histogram — corpus `mathlib`. -/
def mathlibTriad : List Nat :=
  [24775, 24784, 24333, 26320, 25470, 25857, 25039, 25162, 25503, 25000, 24760, 25354, 25722, 24697, 25655, 25082, 24598, 25989, 24914, 25705]
/-- `triad` histogram — corpus `batteries`. -/
def batteriesTriad : List Nat :=
  [444, 503, 473, 461, 468, 459, 442, 465, 443, 493, 485, 488, 468, 476, 508, 528, 483, 524, 528, 463]
/-- `triad` histogram — corpus `lean4`. -/
def lean4Triad : List Nat :=
  [8520, 9198, 8814, 10423, 8979, 8888, 9728, 8573, 8923, 8924, 10060, 8980, 8894, 9113, 9779, 9217, 8630, 10427, 9055, 8753]

/-- `harm` histogram, codes in order `[0, 5, 7, 11, 13]` — corpus `itself`. -/
def itselfHarm : List Nat := [173, 30, 37, 29, 24]
/-- `harm` histogram — corpus `mathlib`. -/
def mathlibHarm : List Nat := [291321, 71529, 60054, 43046, 38769]
/-- `harm` histogram — corpus `batteries`. -/
def batteriesHarm : List Nat := [5598, 1313, 1108, 848, 735]
/-- `harm` histogram — corpus `lean4`. -/
def lean4Harm : List Nat := [103677, 28751, 21219, 16603, 13628]

/-- The harmonic codes, in raster order. -/
def harmCodes : List Nat := [0, 5, 7, 11, 13]

/-! ## §2  Generic, decidable pattern predicates -/

/-- `i` is the **unique strict maximum** index of `l`. -/
def isUniqueMaxAt (l : List Nat) (i : Nat) : Prop :=
  i < l.length ∧ ∀ j, j < l.length → j ≠ i → l.getD j 0 < l.getD i 0

instance (l : List Nat) (i : Nat) : Decidable (isUniqueMaxAt l i) := by
  unfold isUniqueMaxAt
  infer_instance

/-- `i` is **a** (not necessarily unique) maximum index of `l`. -/
def isMaxAt (l : List Nat) (i : Nat) : Prop :=
  i < l.length ∧ ∀ j, j < l.length → l.getD j 0 ≤ l.getD i 0

instance (l : List Nat) (i : Nat) : Decidable (isMaxAt l i) := by
  unfold isMaxAt
  infer_instance

/-- `l` is **strictly decreasing** (each entry greater than the next). -/
def isStrictDecreasing (l : List Nat) : Prop :=
  ∀ i, i + 1 < l.length → l.getD (i + 1) 0 < l.getD i 0

instance (l : List Nat) : Decidable (isStrictDecreasing l) := by
  unfold isStrictDecreasing
  exact decidable_of_iff (∀ i ∈ List.range l.length, i + 1 < l.length → l.getD (i+1) 0 < l.getD i 0)
    (by constructor
        · intro h i hi; exact h i (List.mem_range.2 (by omega)) hi
        · intro h i _ hi; exact h i hi)

/-! ## §3  Harmonic dominance — trivector wins in every corpus -/

/-- Sanity: each `harm` histogram has the five entries. -/
theorem harm_lengths :
    itselfHarm.length = 5 ∧ mathlibHarm.length = 5 ∧
    batteriesHarm.length = 5 ∧ lean4Harm.length = 5 := by native_decide

/-- `itself`: trivector (code 0, index 0) is the unique harmonic maximum. -/
theorem itself_harm_trivector_dominant : isUniqueMaxAt itselfHarm 0 := by native_decide
/-- `mathlib`: trivector is the unique harmonic maximum. -/
theorem mathlib_harm_trivector_dominant : isUniqueMaxAt mathlibHarm 0 := by native_decide
/-- `batteries`: trivector is the unique harmonic maximum. -/
theorem batteries_harm_trivector_dominant : isUniqueMaxAt batteriesHarm 0 := by native_decide
/-- `lean4`: trivector is the unique harmonic maximum. -/
theorem lean4_harm_trivector_dominant : isUniqueMaxAt lean4Harm 0 := by native_decide

/-- **Cross-module pattern.** In all four corpora the trivector cell (harmonic
code `0`) is the unique dominant harmonic cell. -/
theorem harm_trivector_dominant_all :
    isUniqueMaxAt itselfHarm 0 ∧ isUniqueMaxAt mathlibHarm 0 ∧
    isUniqueMaxAt batteriesHarm 0 ∧ isUniqueMaxAt lean4Harm 0 :=
  ⟨itself_harm_trivector_dominant, mathlib_harm_trivector_dominant,
   batteries_harm_trivector_dominant, lean4_harm_trivector_dominant⟩

/-! ## §4  Harmonic monotonicity in the large corpora -/

/-- `mathlib`: harmonic histogram strictly decreasing in code order `0>5>7>11>13`. -/
theorem mathlib_harm_strictDecreasing : isStrictDecreasing mathlibHarm := by native_decide
/-- `batteries`: harmonic histogram strictly decreasing in code order. -/
theorem batteries_harm_strictDecreasing : isStrictDecreasing batteriesHarm := by native_decide
/-- `lean4`: harmonic histogram strictly decreasing in code order. -/
theorem lean4_harm_strictDecreasing : isStrictDecreasing lean4Harm := by native_decide

/-- **Cross-module pattern.** All three large corpora share the identical
strictly-decreasing harmonic profile `trivector > muse > heptad > hemispheres >
recursion`. -/
theorem harm_strictDecreasing_large :
    isStrictDecreasing mathlibHarm ∧ isStrictDecreasing batteriesHarm ∧
    isStrictDecreasing lean4Harm :=
  ⟨mathlib_harm_strictDecreasing, batteries_harm_strictDecreasing,
   lean4_harm_strictDecreasing⟩

/-- The small `itself` corpus is the lone exception: its harmonic histogram is
*not* strictly decreasing (heptad `37` exceeds muse `30`), as OpenCV reported. -/
theorem itself_harm_not_decreasing : ¬ isStrictDecreasing itselfHarm := by native_decide

/-! ## §5  Argmax buckets per view (the OpenCV peak locations) -/

/-- `itself`: brightest `cog` bucket is index `77` (`cog = 78`). -/
theorem itself_cog_argmax : isUniqueMaxAt itselfCog 77 := by native_decide
/-- `mathlib`: brightest `cog` bucket is index `47` (`cog = 48`). -/
theorem mathlib_cog_argmax : isUniqueMaxAt mathlibCog 47 := by native_decide
/-- `batteries`: brightest `cog` bucket is index `55` (`cog = 56`). -/
theorem batteries_cog_argmax : isUniqueMaxAt batteriesCog 55 := by native_decide
/-- `lean4`: brightest `cog` bucket is index `34` (`cog = 35`). -/
theorem lean4_cog_argmax : isUniqueMaxAt lean4Cog 34 := by native_decide

/-- `itself`: brightest `triad` bucket is index `13`. -/
theorem itself_triad_argmax : isUniqueMaxAt itselfTriad 13 := by native_decide
/-- `mathlib`: brightest `triad` bucket is index `3`. -/
theorem mathlib_triad_argmax : isUniqueMaxAt mathlibTriad 3 := by native_decide
/-- `batteries`: brightest `triad` bucket is index `15` — a tied maximum (the
same peak value `528` also occurs at index `18`), so this is a non-unique max. -/
theorem batteries_triad_argmax : isMaxAt batteriesTriad 15 := by native_decide
/-- The `batteries` triad maximum is genuinely tied (also attained at index `18`),
so it is *not* a unique maximum. -/
theorem batteries_triad_tie : isMaxAt batteriesTriad 18 ∧ ¬ isUniqueMaxAt batteriesTriad 15 := by
  native_decide
/-- `lean4`: brightest `triad` bucket is index `17`. -/
theorem lean4_triad_argmax : isUniqueMaxAt lean4Triad 17 := by native_decide

/-! ## §6  Range soundness of the rasters -/

/-- Every datapoint feeding a `cog` raster lands in `1 … 92`, so the 92-bucket
`cog` histograms above are exhaustive (no out-of-range entry was dropped). -/
theorem cog_in_range (h : Nat) : 1 ≤ DualAtlas.cogProj h ∧ DualAtlas.cogProj h ≤ 92 :=
  DualAtlas.cogProj_mem h

/-- Every datapoint feeding a `triad` raster lands in `0 … 19`, so the 20-bucket
`triad` histograms above are exhaustive. -/
theorem triad_in_range (h : Nat) : DualAtlas.triadProj h ≤ 19 :=
  DualAtlas.triadProj_le h

end VisionPatterns
