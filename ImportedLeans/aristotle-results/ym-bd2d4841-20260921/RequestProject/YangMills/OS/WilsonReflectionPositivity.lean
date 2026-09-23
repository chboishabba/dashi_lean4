/-
# Osterwalder–Schrader reflection positivity of the literal Wilson measure

This file proves reflection positivity of the Wilson lattice gauge measure of
`Lattice/Wilson.lean` on the periodic four-dimensional lattice with even time
extent `n + 1 = 2L`, for an arbitrary compact gauge group and any continuous,
conjugation-invariant, inversion-symmetric character (the physical case
`χ = Re tr` on `SU(N)`).

The argument is the one of Osterwalder and Seiler, carried out on the literal
objects:

* every plaquette of the lattice lies either in the closed positive half
  `0 ≤ t ≤ L`, or in the closed negative half, or in one of the two reflection
  planes `t = 0`, `t = L`; this gives the splitting of the Wilson action

  ```
    S = S_plane + S_+ + S_+ ∘ Θ
  ```

  (`wilsonAction_split`), where `Θ` is the literal time reflection of the gauge
  field and the identification of the negative part with the reflected positive
  part (`actionOn_plaqNeg_eq`) is the plaquette identity of
  `OS/WilsonPlaquetteReflection.lean`;
* the product Haar measure factorises through the plane, positive and negative
  link variables (`OS/LinkReflection.lean`);
* the Gram/Fubini computation of `OS/GramPositivity.lean` then gives
  positivity.

Main results:

* `wilsonAction_split` — the splitting of the literal Wilson action;
* `wilson_reflection_positive_unnormalised` — reflection positivity for the
  Boltzmann-weighted product Haar measure;
* `wilson_reflection_positive` — reflection positivity of the literal
  Wilson–Gibbs probability measure:
  `0 ≤ Re ∫ conj (F ∘ Θ) · F dμ_Gibbs` for every bounded measurable observable
  `F` depending only on the links of the closed positive half.

No postulate, authority, or numerical input is used.
-/
import Mathlib
import RequestProject.YangMills.OS.ActionSplitting
import RequestProject.YangMills.OS.WilsonPlaquetteReflection

namespace RequestProject.YangMills.OS

open MeasureTheory Complex
open RequestProject.YangMills.Lattice

variable {n L : ℕ}

/-! ## Plaquettes and their classification -/

/-- A plaquette label: a base site and two directions. -/
abbrev Plaq (n : ℕ) := Site n × Fin 4 × Fin 4

variable (n L)

/-- The plaquettes in the two reflection planes (together with the degenerate
ones, whose holonomy is trivial). -/
def plaqPlane : Finset (Plaq n) :=
  Finset.univ.filter fun p =>
    p.2.1 = p.2.2 ∨ (p.2.1 ≠ 0 ∧ p.2.2 ≠ 0 ∧ (tval p.1 = 0 ∨ tval p.1 = L))

/-- The plaquettes strictly on the positive side. -/
def plaqPos : Finset (Plaq n) :=
  Finset.univ.filter fun p =>
    p.2.1 ≠ p.2.2 ∧
      (if p.2.1 = 0 ∨ p.2.2 = 0 then tval p.1 < L else (0 < tval p.1 ∧ tval p.1 < L))

/-- The plaquettes strictly on the negative side. -/
def plaqNeg : Finset (Plaq n) := Finset.univ \ (plaqPlane n L ∪ plaqPos n L)

variable {n L}

@[simp] theorem mem_plaqPlane {p : Plaq n} :
    p ∈ plaqPlane n L ↔
      (p.2.1 = p.2.2 ∨ (p.2.1 ≠ 0 ∧ p.2.2 ≠ 0 ∧ (tval p.1 = 0 ∨ tval p.1 = L))) := by
  simp [plaqPlane]

@[simp] theorem mem_plaqPos {p : Plaq n} :
    p ∈ plaqPos n L ↔
      (p.2.1 ≠ p.2.2 ∧
        (if p.2.1 = 0 ∨ p.2.2 = 0 then tval p.1 < L else (0 < tval p.1 ∧ tval p.1 < L))) := by
  simp [plaqPos]

@[simp] theorem mem_plaqNeg {p : Plaq n} :
    p ∈ plaqNeg n L ↔ (p ∉ plaqPlane n L ∧ p ∉ plaqPos n L) := by
  simp [plaqNeg]

/-- The reflection of plaquette labels. -/
def plaqRefl (p : Plaq n) : Plaq n := (reflBase p.1 p.2.1 p.2.2, p.2.1, p.2.2)

@[simp] theorem plaqRefl_fst (p : Plaq n) :
    (plaqRefl p).1 = reflBase p.1 p.2.1 p.2.2 := rfl

@[simp] theorem plaqRefl_dir1 (p : Plaq n) : (plaqRefl p).2.1 = p.2.1 := rfl

@[simp] theorem plaqRefl_dir2 (p : Plaq n) : (plaqRefl p).2.2 = p.2.2 := rfl

theorem siteRefl_sub_time_involutive (x : Site n) :
    siteRefl (siteRefl x - unitVec n 0) - unitVec n 0 = x := by
  have h : siteRefl (siteRefl x - unitVec n 0) = x + unitVec n 0 := by
    calc siteRefl (siteRefl x - unitVec n 0)
        = siteRefl (siteRefl x - unitVec n 0 + unitVec n 0) + unitVec n 0 := by
          rw [siteRefl_add_time]; abel
      _ = x + unitVec n 0 := by rw [sub_add_cancel, siteRefl_involutive]
  rw [h]; abel

theorem plaqRefl_involutive (p : Plaq n) : plaqRefl (plaqRefl p) = p := by
  obtain ⟨x, mu, nu⟩ := p
  by_cases hd : mu = 0 ∨ nu = 0
  · simp only [plaqRefl, reflBase, if_pos hd]
    simp [siteRefl_sub_time_involutive]
  · simp only [plaqRefl, reflBase, if_neg hd]
    simp [siteRefl_involutive]

theorem tval_reflBase_time {x : Site n} {mu nu : Fin 4} (h : mu = 0 ∨ nu = 0) :
    tval (reflBase x mu nu) = n - tval x := by
  simp only [reflBase, if_pos h]
  exact tval_siteRefl_sub_time x

theorem tval_reflBase_space {x : Site n} {mu nu : Fin 4} (h : ¬ (mu = 0 ∨ nu = 0)) :
    tval (reflBase x mu nu) = if tval x = 0 then 0 else (n + 1) - tval x := by
  simp only [reflBase, if_neg h]
  exact tval_siteRefl x

theorem plaqRefl_mem_plaqNeg (hN : n + 1 = 2 * L) {p : Plaq n} (hp : p ∈ plaqPos n L) :
    plaqRefl p ∈ plaqNeg n L := by
  rw [mem_plaqPos] at hp
  obtain ⟨hne, hcase⟩ := hp
  have hlt := tval_lt p.1
  by_cases hd : p.2.1 = 0 ∨ p.2.2 = 0
  · rw [if_pos hd] at hcase
    have ht : tval (plaqRefl p).1 = n - tval p.1 := by
      rw [plaqRefl_fst]; exact tval_reflBase_time hd
    refine mem_plaqNeg.2 ⟨?_, ?_⟩
    · rw [mem_plaqPlane]
      simp only [plaqRefl_dir1, plaqRefl_dir2]
      rintro (h | ⟨h1, h2, -⟩)
      · exact hne h
      · rcases hd with h | h
        · exact h1 h
        · exact h2 h
    · rw [mem_plaqPos]
      simp only [plaqRefl_dir1, plaqRefl_dir2]
      rintro ⟨-, hc⟩
      rw [if_pos hd, ht] at hc
      omega
  · rw [if_neg hd] at hcase
    have ht : tval (plaqRefl p).1 = (n + 1) - tval p.1 := by
      rw [plaqRefl_fst, tval_reflBase_space hd, if_neg (by omega : ¬ tval p.1 = 0)]
    refine mem_plaqNeg.2 ⟨?_, ?_⟩
    · rw [mem_plaqPlane]
      simp only [plaqRefl_dir1, plaqRefl_dir2]
      rintro (h | ⟨-, -, h⟩)
      · exact hne h
      · rw [ht] at h; omega
    · rw [mem_plaqPos]
      simp only [plaqRefl_dir1, plaqRefl_dir2]
      rintro ⟨-, hc⟩
      rw [if_neg hd, ht] at hc
      omega

theorem plaqRefl_mem_plaqPos (hN : n + 1 = 2 * L) {p : Plaq n} (hp : p ∈ plaqNeg n L) :
    plaqRefl p ∈ plaqPos n L := by
  rw [mem_plaqNeg, mem_plaqPlane, mem_plaqPos] at hp
  obtain ⟨hplane, hpos⟩ := hp
  have hlt := tval_lt p.1
  have hne : p.2.1 ≠ p.2.2 := fun hc => hplane (Or.inl hc)
  by_cases hd : p.2.1 = 0 ∨ p.2.2 = 0
  · have hcase : ¬ (tval p.1 < L) := by
      intro hc
      exact hpos ⟨hne, by rw [if_pos hd]; exact hc⟩
    rw [mem_plaqPos]
    simp only [plaqRefl_dir1, plaqRefl_dir2]
    refine ⟨hne, ?_⟩
    rw [if_pos hd, plaqRefl_fst, tval_reflBase_time hd]
    omega
  · push_neg at hd
    have hnz : tval p.1 ≠ 0 ∧ tval p.1 ≠ L := by
      constructor <;> intro hc <;>
        exact hplane (Or.inr ⟨hd.1, hd.2, by simp [hc]⟩)
    have hcase : ¬ (0 < tval p.1 ∧ tval p.1 < L) := by
      intro hc
      exact hpos ⟨hne, by rw [if_neg (by tauto)]; exact hc⟩
    rw [mem_plaqPos]
    simp only [plaqRefl_dir1, plaqRefl_dir2]
    refine ⟨hne, ?_⟩
    rw [if_neg (by tauto), plaqRefl_fst, tval_reflBase_space (by tauto),
      if_neg (by omega : ¬ tval p.1 = 0)]
    omega

/-! ## The action, split over the three classes of plaquettes -/

variable {G : Type*} [Group G]

/-- The part of the Wilson action coming from a set of plaquettes. -/
noncomputable def actionOn (beta : ℝ) (chi : G → ℝ) (s : Finset (Plaq n)) (U : Conf n G) : ℝ :=
  -beta * ∑ p ∈ s, chi (plaqHol U p.1 p.2.1 p.2.2)

theorem wilsonAction_eq_actionOn (beta : ℝ) (chi : G → ℝ) (U : Conf n G) :
    wilsonAction beta chi U = actionOn beta chi Finset.univ U := by
  unfold wilsonAction actionOn
  congr 1
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Fintype.sum_prod_type]

theorem actionOn_union_disjoint (beta : ℝ) (chi : G → ℝ) {s t : Finset (Plaq n)}
    (hst : Disjoint s t) (U : Conf n G) :
    actionOn beta chi (s ∪ t) U = actionOn beta chi s U + actionOn beta chi t U := by
  unfold actionOn
  rw [Finset.sum_union hst]
  ring

/-- **The splitting of the literal Wilson action** into a plane part, a positive
part and a negative part. -/
theorem wilsonAction_split (beta : ℝ) (chi : G → ℝ) (U : Conf n G) :
    wilsonAction beta chi U
      = actionOn beta chi (plaqPlane n L) U + actionOn beta chi (plaqPos n L) U
        + actionOn beta chi (plaqNeg n L) U := by
  have hdisj : Disjoint (plaqPlane n L) (plaqPos n L) := by
    rw [Finset.disjoint_left]
    intro p hp hq
    rw [mem_plaqPlane] at hp
    rw [mem_plaqPos] at hq
    rcases hp with h | ⟨h1, h2, h3⟩
    · exact hq.1 h
    · have hd : ¬ (p.2.1 = 0 ∨ p.2.2 = 0) := by tauto
      rw [if_neg hd] at hq
      omega
  have hsub : plaqPlane n L ∪ plaqPos n L ⊆ Finset.univ := Finset.subset_univ _
  have hsum := Finset.sum_sdiff (f := fun p : Plaq n => chi (plaqHol U p.1 p.2.1 p.2.2)) hsub
  have : actionOn beta chi (plaqNeg n L) U
      + actionOn beta chi (plaqPlane n L ∪ plaqPos n L) U
      = actionOn beta chi Finset.univ U := by
    unfold actionOn plaqNeg
    rw [← mul_add, hsum]
  rw [wilsonAction_eq_actionOn, ← this, actionOn_union_disjoint beta chi hdisj]
  ring

/-- **The negative part of the action is the positive part of the reflected
configuration.** -/
theorem actionOn_plaqNeg_eq (hN : n + 1 = 2 * L) (beta : ℝ) {chi : G → ℝ}
    (hconj : ∀ a g : G, chi (a * g * a⁻¹) = chi g) (hinv : ∀ g : G, chi g⁻¹ = chi g)
    (U : Conf n G) :
    actionOn beta chi (plaqNeg n L) U = actionOn beta chi (plaqPos n L) (reflConf hN U) := by
  unfold actionOn
  congr 1
  refine Finset.sum_nbij' plaqRefl plaqRefl (fun a ha => plaqRefl_mem_plaqPos hN ha)
    (fun a ha => plaqRefl_mem_plaqNeg hN ha) (fun a _ => plaqRefl_involutive a)
    (fun a _ => plaqRefl_involutive a) ?_
  intro p _
  have h1 : reflBase (plaqRefl p).1 (plaqRefl p).2.1 (plaqRefl p).2.2 = p.1 :=
    congrArg Prod.fst (plaqRefl_involutive p)
  rw [chi_plaqHol_confRefl hN hconj hinv, h1]
  rfl


/-! ## Locality of the two parts of the action -/

theorem plaqHol_congr {U V : Conf n G} {x : Site n} {mu nu : Fin 4}
    (h1 : U (x, mu) = V (x, mu)) (h2 : U (x + unitVec n mu, nu) = V (x + unitVec n mu, nu))
    (h3 : U (x + unitVec n nu, mu) = V (x + unitVec n nu, mu)) (h4 : U (x, nu) = V (x, nu)) :
    plaqHol U x mu nu = plaqHol V x mu nu := by
  simp only [plaqHol, h1, h2, h3, h4]

/-- A spatial link at a time between the two reflection planes lies in the
closed positive half. -/
theorem spatialLink_mem {z : Site n} {e : Fin 4} (he : e ≠ 0) (h : tval z ≤ L) :
    ((z, e) : Link n) ∈ planeLinks n L ∨ ((z, e) : Link n) ∈ posLinks n L := by
  rcases Nat.eq_zero_or_pos (tval z) with h0 | h0
  · exact Or.inl (mem_planeLinks.2 ⟨he, Or.inl h0⟩)
  · rcases eq_or_lt_of_le h with h2 | h2
    · exact Or.inl (mem_planeLinks.2 ⟨he, Or.inr h2⟩)
    · exact Or.inr (mem_posLinks.2 (by rw [if_neg he]; exact ⟨h0, h2⟩))

/-- A temporal link below the upper reflection plane is positive. -/
theorem temporalLink_mem {z : Site n} (h : tval z < L) :
    ((z, (0 : Fin 4)) : Link n) ∈ posLinks n L :=
  mem_posLinks.2 (by simpa using h)

/-- A spatial link in a reflection plane is a plane link. -/
theorem planeLink_mem {z : Site n} {e : Fin 4} (he : e ≠ 0) (h : tval z = 0 ∨ tval z = L) :
    ((z, e) : Link n) ∈ planeLinks n L := mem_planeLinks.2 ⟨he, h⟩

/-- **Locality of the positive part of the action**: it depends only on the link
variables of the closed positive half. -/
theorem actionOn_plaqPos_local (hN : n + 1 = 2 * L) (beta : ℝ) (chi : G → ℝ) {U V : Conf n G}
    (h : ∀ l : Link n, l ∈ planeLinks n L ∨ l ∈ posLinks n L → U l = V l) :
    actionOn beta chi (plaqPos n L) U = actionOn beta chi (plaqPos n L) V := by
  unfold actionOn
  congr 1
  refine Finset.sum_congr rfl fun p hp => ?_
  obtain ⟨x, mu, nu⟩ := p
  rw [mem_plaqPos] at hp
  obtain ⟨hne, hcase⟩ := hp
  simp only at hne hcase ⊢
  have hlt : tval x < n + 1 := tval_lt x
  have hLn : L ≤ n := by omega
  congr 1
  refine plaqHol_congr (h _ ?_) (h _ ?_) (h _ ?_) (h _ ?_)
  · -- link (x, mu)
    by_cases hmu : mu = 0
    · subst hmu
      rw [if_pos (Or.inl rfl)] at hcase
      exact Or.inr (temporalLink_mem hcase)
    · by_cases hnu : nu = 0
      · subst hnu
        rw [if_pos (Or.inr rfl)] at hcase
        exact spatialLink_mem hmu (by omega)
      · rw [if_neg (by tauto)] at hcase
        exact spatialLink_mem hmu (by omega)
  · -- link (x + mu, nu)
    by_cases hmu : mu = 0
    · subst hmu
      rw [if_pos (Or.inl rfl)] at hcase
      have hnu : nu ≠ 0 := fun hc => hne (by rw [hc])
      have ht : tval (x + unitVec n 0) = tval x + 1 := tval_add_time x (by omega)
      exact spatialLink_mem hnu (by omega)
    · by_cases hnu : nu = 0
      · subst hnu
        rw [if_pos (Or.inr rfl)] at hcase
        have ht : tval (x + unitVec n mu) = tval x := tval_add_spatial x hmu
        exact Or.inr (temporalLink_mem (by omega))
      · rw [if_neg (by tauto)] at hcase
        have ht : tval (x + unitVec n mu) = tval x := tval_add_spatial x hmu
        exact spatialLink_mem hnu (by omega)
  · -- link (x + nu, mu)
    by_cases hnu : nu = 0
    · subst hnu
      rw [if_pos (Or.inr rfl)] at hcase
      have hmu : mu ≠ 0 := fun hc => hne (by rw [hc])
      have ht : tval (x + unitVec n 0) = tval x + 1 := tval_add_time x (by omega)
      exact spatialLink_mem hmu (by omega)
    · by_cases hmu : mu = 0
      · subst hmu
        rw [if_pos (Or.inl rfl)] at hcase
        have ht : tval (x + unitVec n nu) = tval x := tval_add_spatial x hnu
        exact Or.inr (temporalLink_mem (by omega))
      · rw [if_neg (by tauto)] at hcase
        have ht : tval (x + unitVec n nu) = tval x := tval_add_spatial x hnu
        exact spatialLink_mem hmu (by omega)
  · -- link (x, nu)
    by_cases hnu : nu = 0
    · subst hnu
      rw [if_pos (Or.inr rfl)] at hcase
      exact Or.inr (temporalLink_mem hcase)
    · by_cases hmu : mu = 0
      · subst hmu
        rw [if_pos (Or.inl rfl)] at hcase
        exact spatialLink_mem hnu (by omega)
      · rw [if_neg (by tauto)] at hcase
        exact spatialLink_mem hnu (by omega)

/-- **Locality of the plane part of the action**: it depends only on the link
variables in the two reflection planes. -/
theorem actionOn_plaqPlane_local (beta : ℝ) (chi : G → ℝ) {U V : Conf n G}
    (h : ∀ l : Link n, l ∈ planeLinks n L → U l = V l) :
    actionOn beta chi (plaqPlane n L) U = actionOn beta chi (plaqPlane n L) V := by
  unfold actionOn
  congr 1
  refine Finset.sum_congr rfl fun p hp => ?_
  obtain ⟨x, mu, nu⟩ := p
  rw [mem_plaqPlane] at hp
  simp only at hp ⊢
  rcases hp with hdiag | ⟨hmu, hnu, ht⟩
  · subst hdiag
    rw [plaqHol_diag, plaqHol_diag]
  · congr 1
    refine plaqHol_congr (h _ ?_) (h _ ?_) (h _ ?_) (h _ ?_)
    · exact planeLink_mem hmu ht
    · exact planeLink_mem hnu (by rwa [tval_add_spatial x hmu])
    · exact planeLink_mem hmu (by rwa [tval_add_spatial x hnu])
    · exact planeLink_mem hnu ht

/-! ## Continuity and boundedness -/

variable [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]

omit [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] in
theorem continuous_actionOn {chi : G → ℝ} (hchi : Continuous chi) (beta : ℝ)
    (s : Finset (Plaq n)) : Continuous (actionOn (G := G) beta chi s) := by
  unfold actionOn
  exact continuous_const.mul
    (continuous_finset_sum _ fun p _ => hchi.comp (continuous_plaqHol p.1 p.2.1 p.2.2))

omit [T2Space G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G] in
theorem exists_bound_actionOn {chi : G → ℝ} (hchi : Continuous chi) (beta : ℝ)
    (s : Finset (Plaq n)) : ∃ M : ℝ, ∀ U : Conf n G, |actionOn beta chi s U| ≤ M := by
  have hcont : Continuous fun U : Conf n G => |actionOn beta chi s U| :=
    (continuous_actionOn hchi beta s).abs
  obtain ⟨U₀, -, hU₀⟩ :=
    (isCompact_univ (X := Conf n G)).exists_isMaxOn ⟨fun _ => 1, Set.mem_univ _⟩
      hcont.continuousOn
  exact ⟨|actionOn beta chi s U₀|, fun U => hU₀ (Set.mem_univ U)⟩

/-! ## Reflection positivity of the Wilson measure -/

/-- **Reflection positivity of the Boltzmann-weighted product Haar measure.**
For every bounded measurable observable depending only on the links of the
closed positive half `0 ≤ t ≤ L`, the reflected pairing with itself is real and
nonnegative. -/
theorem wilson_reflection_positive_unnormalised (hN : n + 1 = 2 * L) {chi : G → ℝ}
    (hchi : Continuous chi) (hconj : ∀ a g : G, chi (a * g * a⁻¹) = chi g)
    (hinv : ∀ g : G, chi g⁻¹ = chi g) (beta : ℝ)
    {F : Conf n G → ℂ} {MF : ℝ} (hFm : Measurable F) (hFb : ∀ U, ‖F U‖ ≤ MF)
    (hFloc : ∀ U V : Conf n G,
      (∀ l : Link n, l ∈ planeLinks n L ∨ l ∈ posLinks n L → U l = V l) → F U = F V) :
    0 ≤ (∫ U, (starRingEnd ℂ) (F (reflConf hN U)) * F U *
        (Real.exp (-(wilsonAction beta chi U)) : ℂ) ∂(prodHaar (Link n) G)).re ∧
      (∫ U, (starRingEnd ℂ) (F (reflConf hN U)) * F U *
        (Real.exp (-(wilsonAction beta chi U)) : ℂ) ∂(prodHaar (Link n) G)).im = 0 := by
  obtain ⟨M0, hM0⟩ := exists_bound_actionOn (n := n) (G := G) hchi beta (plaqPlane n L)
  obtain ⟨M1, hM1⟩ := exists_bound_actionOn (n := n) (G := G) hchi beta (plaqPos n L)
  refine (wilsonReflData hN).reflection_positive_of_splitting
    (F := F) (S := wilsonAction beta chi) (S0 := actionOn beta chi (plaqPlane n L))
    (Splus := actionOn beta chi (plaqPos n L)) (MF := MF) (MS := max M0 M1)
    hFm hFb ?_ ((continuous_actionOn hchi beta _).measurable)
    (fun U => le_trans (hM0 U) (le_max_left _ _)) ?_
    ((continuous_actionOn hchi beta _).measurable)
    (fun U => le_trans (hM1 U) (le_max_right _ _)) ?_ ?_
  · intro U V hUV
    exact hFloc U V (by simpa using hUV)
  · intro U V hUV
    exact actionOn_plaqPlane_local beta chi (by simpa using hUV)
  · intro U V hUV
    exact actionOn_plaqPos_local hN beta chi (by simpa using hUV)
  · intro U
    rw [wilsonAction_split (L := L) beta chi U, actionOn_plaqNeg_eq hN beta hconj hinv U]
    rfl

/-- **Osterwalder–Schrader reflection positivity of the literal Wilson–Gibbs
measure.**  On the periodic four-dimensional lattice with even time extent
`n + 1 = 2L`, with an arbitrary compact gauge group and any continuous
conjugation-invariant character with `χ(g⁻¹) = χ(g)`, the Wilson–Gibbs
probability measure satisfies

```
  Re ∫ conj (F (Θ U)) · F (U) dμ(U) ≥ 0
```

for every bounded measurable observable `F` depending only on the link
variables of the closed positive half `0 ≤ t ≤ L`, where `Θ` is the time
reflection of the gauge field. -/
theorem wilson_reflection_positive (hN : n + 1 = 2 * L) {chi : G → ℝ}
    (hchi : Continuous chi) (hconj : ∀ a g : G, chi (a * g * a⁻¹) = chi g)
    (hinv : ∀ g : G, chi g⁻¹ = chi g) (beta : ℝ)
    {F : Conf n G → ℂ} {MF : ℝ} (hFm : Measurable F) (hFb : ∀ U, ‖F U‖ ≤ MF)
    (hFloc : ∀ U V : Conf n G,
      (∀ l : Link n, l ∈ planeLinks n L ∨ l ∈ posLinks n L → U l = V l) → F U = F V) :
    0 ≤ (∫ U, (starRingEnd ℂ) (F (reflConf hN U)) * F U ∂(gibbs n G beta chi)).re := by
  have hden : ∀ᵐ U ∂(prodHaar (Link n) G), gibbsDensity (n := n) beta chi U < ⊤ :=
    Filter.Eventually.of_forall fun U => by
      simp [gibbsDensity, ENNReal.ofReal_lt_top]
  have hrewrite : ∫ U, (starRingEnd ℂ) (F (reflConf hN U)) * F U ∂(gibbs n G beta chi)
      = ((partition n G beta chi)⁻¹).toReal •
        ∫ U, (starRingEnd ℂ) (F (reflConf hN U)) * F U *
          (Real.exp (-(wilsonAction beta chi U)) : ℂ) ∂(prodHaar (Link n) G) := by
    rw [gibbs, integral_smul_measure, gibbsUnnorm,
      integral_withDensity_eq_integral_toReal_smul (measurable_gibbsDensity hchi beta) hden]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
    have hval : (gibbsDensity (n := n) beta chi U).toReal
        = Real.exp (-(wilsonAction beta chi U)) := by
      simp [gibbsDensity, ENNReal.toReal_ofReal (Real.exp_pos _).le]
    show (gibbsDensity (n := n) beta chi U).toReal • ((starRingEnd ℂ) (F (reflConf hN U)) * F U)
        = (starRingEnd ℂ) (F (reflConf hN U)) * F U * (Real.exp (-(wilsonAction beta chi U)) : ℂ)
    rw [hval, Complex.real_smul]
    ring
  rw [hrewrite]
  rw [Complex.smul_re]
  exact mul_nonneg ENNReal.toReal_nonneg
    (wilson_reflection_positive_unnormalised hN hchi hconj hinv beta hFm hFb hFloc).1

end RequestProject.YangMills.OS

/-! ## Axiom audit -/

section Audit

open RequestProject.YangMills.OS

#print axioms wilsonAction_split
#print axioms actionOn_plaqNeg_eq
#print axioms wilson_reflection_positive_unnormalised
#print axioms wilson_reflection_positive

end Audit
