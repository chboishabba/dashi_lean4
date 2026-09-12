/-
# The spine, end to end

A single record whose fields are the actual statements of this tranche, and one
inhabitant of it built from the proved theorems.  Nothing here can be satisfied
by a placeholder: each field is the theorem itself, so the inhabitant
`Spine.spineLedger` is a machine-checked receipt that the spine holds together.

Read the fields as the spine's five stages:

1. *carrier with a distinguished fixed mode* — `mean_splitting`;
2. *symmetry acting on the transverse fibre* — `ternary_no_invariant_line`,
   `binary_collapse`, `critical_line_fixed_locus`;
3. *descent to real observables* — `descent_fixed_field`;
4. *nondegeneracy witness* — `anchored_coercivity`, `five_transverse_planes`,
   `cuisine_plane`, and the negative `degeneracy_control`;
5. *the discipline* — `ogg_grid`, `ogg_no_equivariant_labelling`,
   `equal_cardinality_gives_no_canonical_map`.
-/
import Mathlib
import Spine.AnchoredGram
import Spine.TernaryPhase
import Spine.TraceNorm
import Spine.MeanSplit
import Spine.Observer
import Spine.TritCarrier
import Spine.OggGrid
import Spine.FixedLocus
import Spine.EqualCardinality

open Matrix RealInnerProductSpace ComplexConjugate

namespace Spine

/-- The spine as a single record of statements. -/
structure SpineLedger where
  /-- Anchored exterior coercivity in arbitrary rank. -/
  anchored_coercivity :
    ∀ (V : Type) (_ : NormedAddCommGroup V) (_ : InnerProductSpace ℝ V) (r : ℕ)
      (f t₀ : V) (t : Fin r → V), ⟪f, t₀⟫ = 0 → (∀ j, ⟪f, t j⟫ = 0) →
      ‖f‖ ^ 2 * (Matrix.gram ℝ t).det ≤ (Matrix.gram ℝ (Fin.cons (f + t₀) t)).det
  /-- Every vector splits as constant part plus mean-zero part, orthogonally. -/
  mean_splitting :
    ∀ (n : ℕ) (_ : NeZero n) (x : EuclideanSpace ℝ (Fin n)),
      MeanSplit.meanPart x + MeanSplit.fluct x = x ∧ ⟪MeanSplit.meanPart x, MeanSplit.fluct x⟫ = 0
  /-- The ternary transverse plane carries no invariant line. -/
  ternary_no_invariant_line :
    ∀ x : RealC3.V, x ∈ RealC3.transverse → x ≠ 0 → ∀ c : ℝ, RealC3.shift x ≠ c • x
  /-- `ℝ[C₃]` splits literally as fixed line ⊕ transverse plane. -/
  ternary_realification : IsCompl RealC3.fixedSub RealC3.transverse
  /-- The transverse plane is an irreducible real representation of `C₃`. -/
  ternary_irreducible :
    ∀ W : Submodule ℝ RealC3.V, W ≤ RealC3.transverse → (∀ x ∈ W, RealC3.shift x ∈ W) →
      W = ⊥ ∨ W = RealC3.transverse
  /-- The binary transverse sector, by contrast, is an eigenline. -/
  binary_collapse : ∀ x : RealC2.V, x ∈ RealC2.transverse → RealC2.swap x = -x
  /-- The maximal real subfield of `ℚ(ζ₃)` is `ℚ`. -/
  descent_fixed_field : ∀ u v : ℚ, conj (Cyc.mk u v) = Cyc.mk u v ↔ v = 0
  /-- The critical line is the fixed locus of an explicit involution. -/
  critical_line_fixed_locus : ∀ s : ℂ, s.re = 1 / 2 ↔ 1 - s = conj s
  /-- Five modes with witnesses are five genuine transverse planes. -/
  five_transverse_planes :
    ∀ a t : Fin 5 → EuclideanSpace ℝ (Fin 3), (∀ i, MeanSplit.avg (a i) ≠ 0) →
      (∀ i, MeanSplit.fluct (t i) ≠ 0) → ∀ i, 0 < area2 (a i) (MeanSplit.fluct (t i))
  /-- The corpus's balanced-ternary digit carrier is a `C₃`-carrier: its
  rotation is intertwined with the cyclic shift, and its negation with a linear
  reflection satisfying the dihedral relation. -/
  trit_carrier_equivariant :
    (∀ f : AgdaMirror.DASHIAlgebra.Trit → ℝ,
        RealC3.shift (TritCarrier.embed f)
          = TritCarrier.embed (f ∘ AgdaMirror.TritBridge.rotTrit)) ∧
      (∀ x : RealC3.V, TritCarrier.reflect (RealC3.shift x)
          = RealC3.shift (RealC3.shift (TritCarrier.reflect x)))
  /-- Negation is not rotation, as linear maps on the ternary carrier. -/
  trit_reflection_ne_rotation : TritCarrier.reflect ≠ RealC3.shift
  /-- The cuisine taste carrier is an instance of the same theorem. -/
  cuisine_plane :
    ∀ (p q : Cuisine.SensoryCore.SensoryProfile) (d : Cuisine.SensoryCore.TasteDimension)
      (i j : Fin 5), 0 < p.tasteIntensity d → (∃ k, Cuisine.tasteIndex k = d) →
      q.tasteIntensity (Cuisine.tasteIndex i) ≠ q.tasteIntensity (Cuisine.tasteIndex j) →
      0 < area2 (Cuisine.tasteVec p) (MeanSplit.fluct (Cuisine.tasteVec q))
  /-- Degenerate instances prove nothing. -/
  degeneracy_control :
    ∀ (n : ℕ) (_ : NeZero n) (x y : EuclideanSpace ℝ (Fin n)), (∀ i j, y i = y j) →
      area2 x (MeanSplit.fluct y) = 0
  /-- The affine grid sits inside the Ogg set. -/
  ogg_grid : ∀ i < 3, ∀ j < 2, Ogg.gridMap i j ∈ Ogg.oggSet
  /-- The internal `5 × 3` carrier does not transport onto the Ogg set. -/
  ogg_no_equivariant_labelling :
    ∀ e : Fin 5 × Fin 3 ≃ {p : ℕ // p ∈ Ogg.oggSet},
      (∀ x, Ogg.cmClass ((e (Ogg.internalShift x)).1) = Ogg.cmClass ((e x).1)) → False
  /-- Equal cardinality never gives a canonical map. -/
  equal_cardinality_gives_no_canonical_map :
    ∀ (α β : Type) (_ : Fintype α) (_ : Fintype β) (_ : DecidableEq α),
      Fintype.card α = Fintype.card β → 2 ≤ Fintype.card α → ∃ e f : α ≃ β, e ≠ f

/-- The spine holds: every field is discharged by the corresponding theorem. -/
theorem spineLedger : SpineLedger where
  anchored_coercivity := fun _ _ _ _ f t₀ t h₀ ht => det_gram_anchored_ge f t₀ t h₀ ht
  mean_splitting := fun _ _ x => ⟨MeanSplit.meanPart_add_fluct x, MeanSplit.inner_meanPart_fluct x x⟩
  ternary_no_invariant_line := fun _ hx hx0 c => RealC3.no_real_eigenvector_transverse hx hx0 c
  ternary_realification := RealC3.isCompl_fixedSub_transverse
  ternary_irreducible := RealC3.transverse_irreducible
  binary_collapse := fun _ hx => RealC2.swap_eq_neg_on_transverse hx
  descent_fixed_field := Cyc.conj_fixed_iff_rational
  critical_line_fixed_locus := re_eq_half_iff
  five_transverse_planes := fun a t ha ht => monster_five_transverse_planes a t ha ht
  trit_carrier_equivariant := ⟨TritCarrier.embed_rot, TritCarrier.reflect_shift⟩
  trit_reflection_ne_rotation := TritCarrier.reflect_ne_shift
  cuisine_plane := fun _ _ _ _ _ hd hmem hij => Cuisine.taste_plane_pos hd hmem hij
  degeneracy_control := fun _ _ x y hy => degenerate_observer_area_zero x y hy
  ogg_grid := Ogg.grid_subset
  ogg_no_equivariant_labelling := Ogg.no_equivariant_labelling
  equal_cardinality_gives_no_canonical_map := fun _ _ _ _ _ hcard h2 =>
    exists_two_distinct_equivs hcard h2

end Spine
