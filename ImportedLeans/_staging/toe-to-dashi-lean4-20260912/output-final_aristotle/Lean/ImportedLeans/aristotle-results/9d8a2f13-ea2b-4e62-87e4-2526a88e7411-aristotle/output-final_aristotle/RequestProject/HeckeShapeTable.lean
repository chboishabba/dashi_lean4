/-
# The twenty-six shapes, measured

`RequestProject/HeckeShapes.lean` defines the shape of a sporadic group in Hecke space: the
prime powers `p^k`, `k ≤ v_p(|G|)`, at which the group lights up the plotted coefficient
`τ(p^k)/p^{11k/2}`.  This file measures the part of each shape that is visible in the window
`n ≤ 256` of `visualization/modular-tau-fibers.svg`:

```
visPoints G = { p^k : k ≤ v_p(|G|), p^k ≤ 256 },   visMass G = ∑ |τ(n)/n^{11/2}| over visPoints G.
```

Every visible point is one of the thirty-six prime powers already pinned down to nine decimals in
`RequestProject/FiberSumsMulti.lean` and `RequestProject/FiberSumsSingle.lean`, so each of the
twenty-six masses is proved to lie within `10⁻⁷` of an explicit rational (`visMass_close`).

The conclusions are the ones the picture suggests:

* the **shape efficiency** `visMass G / dim G` — how much visible shape a group buys per Hecke
  coordinate — is *smallest for the Monster*, among all twenty-six groups
  (`shapeEfficiency_monster_min`), and largest for small groups;
* `M11`, `J2` and `M24` are each worth a large fraction of the whole Monster shape
  (`visMass_m11_share`, `visMass_j2_share`, `visMass_m24_share`), at two-and-a-half to three
  times the Monster's efficiency;
* together the three of them light up sixteen of the Monster's thirty-one visible points and
  carry more than `48 %` of its visible mass (`unionMass_share`).
-/
import RequestProject.HeckeShapes

namespace HeckeShapes

open FiberSums RamanujanTau

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-! ## The visible part of a shape -/

/-- The exponents of `p` that the pair `(p, e)` makes visible in the window `n ≤ 256`. -/
def visExponents (pe : ℕ × ℕ) : List ℕ := (List.range' 1 pe.2).filter fun k => pe.1 ^ k ≤ 256

/-- The visible shape of `G`: the prime powers `p^k` with `k ≤ v_p(|G|)` and `p^k ≤ 256`. -/
def visPoints (G : Sporadic.Group) : List ℕ :=
  G.factors.flatMap fun pe => (visExponents pe).map fun k => pe.1 ^ k

/-- The Hecke mass of a list of plotted points. -/
noncomputable def massList (l : List ℕ) : ℝ := (l.map fun n => |normTau n|).sum

/-- The visible Hecke mass of the shape of `G`. -/
noncomputable def visMass (G : Sporadic.Group) : ℝ := massList (visPoints G)

/-- The number of visible points of the shape of `G`. -/
def visDim (G : Sporadic.Group) : ℕ := (visPoints G).length

/-- The shape efficiency of `G`: visible Hecke mass per Hecke coordinate. -/
noncomputable def shapeEfficiency (G : Sporadic.Group) : ℝ := visMass G / dim G

/-! ## The thirty-six plotted values -/

/-- The thirty-six prime powers `p^k ≤ 256` over the first twenty primes: the highlighted points
of `visualization/modular-tau-fibers.svg`. -/
def plottedPowers : List ℕ :=
  [2, 4, 8, 16, 32, 64, 128, 256, 3, 9, 27, 81, 243, 5, 25, 125, 7, 49, 11, 121, 13, 169,
   17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71]

/-- The proved value of `|τ(n)/n^{11/2}|` at each plotted point, to nine decimals. -/
def refAbs : ℕ → ℚ
  | 2 => 0.530330085890
  | 4 => 0.718750000000
  | 8 => 0.911504835123
  | 16 => 0.235351562500
  | 32 => 1.036318849478
  | 64 => 0.314239501953
  | 128 => 0.869668187417
  | 256 => 0.775450706482
  | 3 => 0.598733612493
  | 9 => 0.641518061271
  | 27 => 0.982832038797
  | 81 => 0.053063484208
  | 243 => 1.014602930389
  | 5 => 0.691213333205
  | 25 => 0.522224128000
  | 125 => 1.052181613400
  | 7 => 0.376547696559
  | 49 => 0.858211832216
  | 11 => 1.000872909497
  | 121 => 0.001746580965
  | 13 => 0.431561303293
  | 169 => 0.813754841500
  | 17 => 1.179650499416
  | 19 => 0.987802787127
  | 23 => 0.603975104681
  | 29 => 1.162514717339
  | 31 => 0.331512211057
  | 37 => 0.431986947257
  | 41 => 0.415345299834
  | 43 => 0.017765278869
  | 47 => 1.709172005305
  | 53 => 0.524240730569
  | 59 => 0.944962683061
  | 61 => 1.054569884035
  | 67 => 1.400911795679
  | 71 => 0.644061971436
  | _ => 0

/-- The reference mass of a list of plotted points. -/
def refMassList (l : List ℕ) : ℚ := (l.map refAbs).sum

/-- The reference mass of the visible shape of `G`. -/
def refMass (G : Sporadic.Group) : ℚ := refMassList (visPoints G)

/-- Every plotted point's normalised coefficient is within `10⁻⁹` of its reference value. -/
theorem abs_normTau_sub_refAbs {n : ℕ} (hn : n ∈ plottedPowers) :
    |(|normTau n| - (refAbs n : ℝ))| ≤ 1e-9 := by
  fin_cases hn
  · simp only [refAbs]
    push_cast
    exact absApprox_2
  · simp only [refAbs]
    push_cast
    exact absApprox_4
  · simp only [refAbs]
    push_cast
    exact absApprox_8
  · simp only [refAbs]
    push_cast
    exact absApprox_16
  · simp only [refAbs]
    push_cast
    exact absApprox_32
  · simp only [refAbs]
    push_cast
    exact absApprox_64
  · simp only [refAbs]
    push_cast
    exact absApprox_128
  · simp only [refAbs]
    push_cast
    exact absApprox_256
  · simp only [refAbs]
    push_cast
    exact absApprox_3
  · simp only [refAbs]
    push_cast
    exact absApprox_9
  · simp only [refAbs]
    push_cast
    exact absApprox_27
  · simp only [refAbs]
    push_cast
    exact absApprox_81
  · simp only [refAbs]
    push_cast
    exact absApprox_243
  · simp only [refAbs]
    push_cast
    exact absApprox_5
  · simp only [refAbs]
    push_cast
    exact absApprox_25
  · simp only [refAbs]
    push_cast
    exact absApprox_125
  · simp only [refAbs]
    push_cast
    exact absApprox_7
  · simp only [refAbs]
    push_cast
    exact absApprox_49
  · simp only [refAbs]
    push_cast
    exact absApprox_11
  · simp only [refAbs]
    push_cast
    exact absApprox_121
  · simp only [refAbs]
    push_cast
    exact absApprox_13
  · simp only [refAbs]
    push_cast
    exact absApprox_169
  · simp only [refAbs]
    push_cast
    exact absApprox_17
  · simp only [refAbs]
    push_cast
    exact absApprox_19
  · simp only [refAbs]
    push_cast
    exact absApprox_23
  · simp only [refAbs]
    push_cast
    exact absApprox_29
  · simp only [refAbs]
    push_cast
    exact absApprox_31
  · simp only [refAbs]
    push_cast
    exact absApprox_37
  · simp only [refAbs]
    push_cast
    exact absApprox_41
  · simp only [refAbs]
    push_cast
    exact absApprox_43
  · simp only [refAbs]
    push_cast
    exact absApprox_47
  · simp only [refAbs]
    push_cast
    exact absApprox_53
  · simp only [refAbs]
    push_cast
    exact absApprox_59
  · simp only [refAbs]
    push_cast
    exact absApprox_61
  · simp only [refAbs]
    push_cast
    exact absApprox_67
  · simp only [refAbs]
    push_cast
    exact absApprox_71

/-- Summing the pointwise bounds along a list. -/
theorem abs_massList_sub_refMassList (l : List ℕ) (h : ∀ n ∈ l, n ∈ plottedPowers) :
    |massList l - (refMassList l : ℝ)| ≤ l.length * 1e-9 := by
  induction l with
  | nil => simp [massList, refMassList]
  | cons a t ih =>
      have hhead : |(|normTau a| - (refAbs a : ℝ))| ≤ 1e-9 :=
        abs_normTau_sub_refAbs (h a (List.mem_cons_self ..))
      have htail := ih fun n hn => h n (List.mem_cons_of_mem _ hn)
      have hsplit : massList (a :: t) - (refMassList (a :: t) : ℝ)
          = (|normTau a| - (refAbs a : ℝ)) + (massList t - (refMassList t : ℝ)) := by
        simp only [massList, refMassList, List.map_cons, List.sum_cons, Rat.cast_add]
        ring
      have := abs_add_le (|normTau a| - (refAbs a : ℝ)) (massList t - (refMassList t : ℝ))
      rw [hsplit]
      have hlen : ((a :: t).length : ℝ) * 1e-9 = 1e-9 + t.length * 1e-9 := by
        simp [List.length_cons]
        ring
      rw [hlen]
      linarith

/-- Every visible point of every sporadic shape is one of the thirty-six plotted points. -/
theorem visPoints_subset : ∀ G ∈ Sporadic.groups, ∀ n ∈ visPoints G, n ∈ plottedPowers := by
  decide

/-- No shape has more than thirty-one visible points (the Monster's own count). -/
theorem visDim_le : ∀ G ∈ Sporadic.groups, visDim G ≤ 31 := by decide

/-- **Each of the twenty-six visible masses, to seven decimals.** -/
theorem visMass_close {G : Sporadic.Group} (hG : G ∈ Sporadic.groups) :
    |visMass G - (refMass G : ℝ)| ≤ 1e-7 := by
  have h := abs_massList_sub_refMassList (visPoints G) (visPoints_subset G hG)
  have hlen : ((visPoints G).length : ℝ) ≤ 31 := by
    exact_mod_cast visDim_le G hG
  have : ((visPoints G).length : ℝ) * 1e-9 ≤ 31 * 1e-9 := by
    have : (0 : ℝ) ≤ 1e-9 := by norm_num
    nlinarith
  rw [visMass, refMass]
  linarith

/-! ## Comparisons

All the comparisons below are proved by combining the `10⁻⁷` bound `visMass_close` with an exact
rational inequality between the reference masses.
-/

theorem dim_pos : ∀ G ∈ Sporadic.groups, 0 < dim G := by decide

/-- Transfer of a rational comparison of masses to the real ones. -/
theorem visMass_gt_of_rat {G : Sporadic.Group} (hG : G ∈ Sporadic.groups) {c : ℚ} (hc : 0 ≤ c)
    (h : c * refMass Sporadic.monster + c / 10 ^ 7 + 1 / 10 ^ 7 < refMass G) :
    (c : ℝ) * visMass Sporadic.monster < visMass G := by
  have hM := abs_le.1 (visMass_close Sporadic.monster_mem)
  have hG' := abs_le.1 (visMass_close hG)
  have hR : ((c * refMass Sporadic.monster + c / 10 ^ 7 + 1 / 10 ^ 7 : ℚ) : ℝ)
      < ((refMass G : ℚ) : ℝ) := by exact_mod_cast h
  push_cast at hR
  have hc' : (0 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc
  nlinarith [mul_nonneg hc'
    (by linarith [hM.2] : (0 : ℝ) ≤ ((refMass Sporadic.monster : ℝ) + 1e-7)
      - visMass Sporadic.monster), hM.1, hM.2, hG'.1, hG'.2]

/-- Transfer of a rational comparison of shape efficiencies to the real ones. -/
theorem shapeEfficiency_gt_of_rat {G : Sporadic.Group} (hG : G ∈ Sporadic.groups) {c : ℚ}
    (hc : 0 ≤ c)
    (h : c * (refMass Sporadic.monster * (dim G : ℚ)) + c * (dim G : ℚ) / 10 ^ 7 + 95 / 10 ^ 7
      < refMass G * 95) :
    (c : ℝ) * shapeEfficiency Sporadic.monster < shapeEfficiency G := by
  have hM := abs_le.1 (visMass_close Sporadic.monster_mem)
  have hG' := abs_le.1 (visMass_close hG)
  have hR : ((c * (refMass Sporadic.monster * (dim G : ℚ)) + c * (dim G : ℚ) / 10 ^ 7
      + 95 / 10 ^ 7 : ℚ) : ℝ) < ((refMass G * 95 : ℚ) : ℝ) := by exact_mod_cast h
  push_cast at hR
  have hc' : (0 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc
  have hd : (0 : ℝ) < (dim G : ℝ) := by exact_mod_cast dim_pos G hG
  have hdM : (0 : ℝ) < (dim Sporadic.monster : ℝ) := by
    rw [dim_monster]; norm_num
  have hkey : (c : ℝ) * visMass Sporadic.monster * (dim G : ℝ)
      < visMass G * (dim Sporadic.monster : ℝ) := by
    have hprod : (0 : ℝ) ≤ ((c : ℝ) * (dim G : ℝ))
        * (((refMass Sporadic.monster : ℝ) + 1e-7) - visMass Sporadic.monster) :=
      mul_nonneg (mul_nonneg hc' hd.le) (by linarith [hM.2])
    rw [dim_monster]
    push_cast
    nlinarith [hG'.1, hG'.2]
  rw [shapeEfficiency, shapeEfficiency, ← mul_div_assoc, div_lt_div_iff₀ hdM hd]
  linarith

/-- **The Monster has the least efficient shape of all twenty-six sporadic groups**: every other
sporadic group buys more visible Hecke mass per Hecke coordinate than the Monster does. -/
theorem shapeEfficiency_monster_min {G : Sporadic.Group} (hG : G ∈ Sporadic.groups)
    (hne : G ≠ Sporadic.monster) :
    shapeEfficiency Sporadic.monster < shapeEfficiency G := by
  have hrat : ∀ H ∈ Sporadic.groups, H ≠ Sporadic.monster →
      (1 : ℚ) * (refMass Sporadic.monster * (dim H : ℚ)) + 1 * (dim H : ℚ) / 10 ^ 7 + 95 / 10 ^ 7
        < refMass H * 95 := by native_decide
  have := shapeEfficiency_gt_of_rat hG (c := 1) (by norm_num) (hrat G hG hne)
  simpa using this

/-! ## Three small groups doing a lot of the work -/

/-- The smallest Mathieu group, `|M11| = 2⁴·3²·5·11 = 7920`. -/
def m11 : Sporadic.Group := ⟨"M11", [(2, 4), (3, 2), (5, 1), (11, 1)]⟩

/-- The largest Mathieu group, `|M24| = 2¹⁰·3³·5·7·11·23`. -/
def m24 : Sporadic.Group := ⟨"M24", [(2, 10), (3, 3), (5, 1), (7, 1), (11, 1), (23, 1)]⟩

/-- The Hall–Janko group, `|J2| = 2⁷·3³·5²·7`. -/
def j2 : Sporadic.Group := ⟨"J2", [(2, 7), (3, 3), (5, 2), (7, 1)]⟩

theorem m11_mem : m11 ∈ Sporadic.groups := by decide
theorem m24_mem : m24 ∈ Sporadic.groups := by decide
theorem j2_mem : j2 ∈ Sporadic.groups := by decide

theorem dim_m11 : dim m11 = 8 := by decide
theorem dim_m24 : dim m24 = 17 := by decide
theorem dim_j2 : dim j2 = 13 := by decide

/-- `M11`, of order `7920`, carries more than `23 %` of the Monster's visible Hecke mass. -/
theorem visMass_m11_share : (0.23 : ℝ) * visMass Sporadic.monster < visMass m11 := by
  have h := visMass_gt_of_rat (c := 23 / 100) m11_mem (by norm_num) (by native_decide)
  norm_num at h ⊢
  linarith

/-- `J2` carries more than `37 %` of the Monster's visible Hecke mass. -/
theorem visMass_j2_share : (0.37 : ℝ) * visMass Sporadic.monster < visMass j2 := by
  have h := visMass_gt_of_rat (c := 37 / 100) j2_mem (by norm_num) (by native_decide)
  norm_num at h ⊢
  linarith

/-- `M24` carries more than `45 %` of the Monster's visible Hecke mass. -/
theorem visMass_m24_share : (0.45 : ℝ) * visMass Sporadic.monster < visMass m24 := by
  have h := visMass_gt_of_rat (c := 45 / 100) m24_mem (by norm_num) (by native_decide)
  norm_num at h ⊢
  linarith

/-- `M11` is more than `2.8` times as efficient as the Monster. -/
theorem shapeEfficiency_m11 :
    (2.8 : ℝ) * shapeEfficiency Sporadic.monster < shapeEfficiency m11 := by
  have h := shapeEfficiency_gt_of_rat (c := 28 / 10) m11_mem (by norm_num) (by native_decide)
  norm_num at h ⊢
  linarith

/-- `J2` is more than `2.7` times as efficient as the Monster. -/
theorem shapeEfficiency_j2 :
    (2.7 : ℝ) * shapeEfficiency Sporadic.monster < shapeEfficiency j2 := by
  have h := shapeEfficiency_gt_of_rat (c := 27 / 10) j2_mem (by norm_num) (by native_decide)
  norm_num at h ⊢
  linarith

/-- `M24` is more than `2.5` times as efficient as the Monster. -/
theorem shapeEfficiency_m24 :
    (2.5 : ℝ) * shapeEfficiency Sporadic.monster < shapeEfficiency m24 := by
  have h := shapeEfficiency_gt_of_rat (c := 25 / 10) m24_mem (by norm_num) (by native_decide)
  norm_num at h ⊢
  linarith

/-- The visible shape of `M11` sits inside the visible shape of `M24`: the shapes nest. -/
theorem visPoints_m11_subset_m24 : ∀ n ∈ visPoints m11, n ∈ visPoints m24 := by decide

/-- The plotted window `n ≤ 256` does not separate every pair of groups: `Co2` and `Co3` light
up exactly the same points there, although their shapes have different dimensions
(`30` against `23`). -/
theorem visPoints_co2_eq_co3 :
    visPoints ⟨"Co2", [(2, 18), (3, 6), (5, 3), (7, 1), (11, 1), (23, 1)]⟩
      = visPoints ⟨"Co3", [(2, 10), (3, 7), (5, 3), (7, 1), (11, 1), (23, 1)]⟩ := by decide

theorem dim_co2_ne_dim_co3 :
    dim ⟨"Co2", [(2, 18), (3, 6), (5, 3), (7, 1), (11, 1), (23, 1)]⟩
      ≠ dim ⟨"Co3", [(2, 10), (3, 7), (5, 3), (7, 1), (11, 1), (23, 1)]⟩ := by decide

/-! ## The three shapes together -/

/-- The points lit up by at least one of `M11`, `M24`, `J2`. -/
def unionPoints : List ℕ := (visPoints m11 ++ visPoints m24 ++ visPoints j2).dedup

/-- The Hecke mass carried jointly by the three small groups. -/
noncomputable def unionMass : ℝ := massList unionPoints

/-- The three small groups light up sixteen distinct points. -/
theorem unionPoints_length : unionPoints.length = 16 := by decide

/-- All sixteen are points of the Monster's own visible shape, which has thirty-one. -/
theorem unionPoints_subset_monster : ∀ n ∈ unionPoints, n ∈ visPoints Sporadic.monster := by decide

theorem visDim_monster : visDim Sporadic.monster = 31 := by decide

theorem unionPoints_plotted : ∀ n ∈ unionPoints, n ∈ plottedPowers := by decide

/-- **Sixteen of the Monster's thirty-one visible points, and more than `48 %` of its visible
Hecke mass, are already accounted for by `M11`, `M24` and `J2` alone.** -/
theorem unionMass_share : (0.48 : ℝ) * visMass Sporadic.monster < unionMass := by
  have hU := abs_le.1 (abs_massList_sub_refMassList unionPoints unionPoints_plotted)
  have hM := abs_le.1 (visMass_close Sporadic.monster_mem)
  have hlen : (unionPoints.length : ℝ) = 16 := by rw [unionPoints_length]; norm_num
  have hrat : (48 / 100 : ℚ) * refMass Sporadic.monster + 48 / 10 ^ 9 + 16 / 10 ^ 9
      < refMassList unionPoints := by native_decide
  have hR : (((48 / 100 : ℚ) * refMass Sporadic.monster + 48 / 10 ^ 9 + 16 / 10 ^ 9 : ℚ) : ℝ)
      < ((refMassList unionPoints : ℚ) : ℝ) := by exact_mod_cast hrat
  push_cast at hR
  rw [hlen] at hU
  rw [unionMass]
  norm_num at hU
  linarith [hM.1, hM.2, hU.1, hU.2]

end HeckeShapes
