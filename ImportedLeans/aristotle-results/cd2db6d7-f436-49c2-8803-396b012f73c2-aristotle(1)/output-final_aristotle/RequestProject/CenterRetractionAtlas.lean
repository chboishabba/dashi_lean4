import RequestProject.CenterRetraction
import RequestProject.CenterRetractionMore
import RequestProject.CenterRetractionProd
import RequestProject.CenterRetractionPi
import RequestProject.CenterRetractionSplit
import RequestProject.CenterRetractionPerm
import RequestProject.CenterRetractionSharpness
import RequestProject.CenterRetractionHeredity
import RequestProject.CenterRetractionSmall
import RequestProject.DihedralCenterRetraction
import RequestProject.DihedralInfinite
import RequestProject.QuaternionCenterRetraction
import RequestProject.GeneralLinearCenterRetraction
import RequestProject.GeneralLinearPositive
import RequestProject.GeneralLinearEven

/-!
# The atlas of the center-retraction half of the project

This file contains no new mathematics: it is a single statement, `centerRetractionAtlas`,
collecting every classification result about `HasCenterRetraction` proved in this project, so
that the whole group-theoretic half can be read off one theorem — and so that any future
change that breaks one of the classifications breaks this file.

The twelve clauses, in order:

1. abelian groups retract;
2. centerless groups retract;
3. the general criterion: a retraction exists iff `Z(G)` has a complement;
4. the splitting form: iff `G ≅ N × Z(G)` with `N` centerless;
5. no nonabelian nilpotent group retracts (in particular no nonabelian finite `p`-group);
6. Schur–Zassenhaus: coprimality of `|Z(G)|` and `[G : Z(G)]` suffices;
7. binary products retract iff both factors do;
8. arbitrary products retract iff every factor does;
9. the dihedral classification `D_n`: iff `n = 0` or `4 ∤ n`;
10. the dicyclic classification `Q_n` (order `4n`): iff `n < 2`;
11. symmetric and alternating groups always retract, `GL₂` over a ring with `2 ≠ 0` never does;
12. sharpness and non-heredity: disjointness of `[G,G]` and `Z(G)` is necessary but not
    sufficient, and the property passes to neither subgroups nor quotients;
13. every finite group of squarefree order retracts, every group of order `< 8` retracts, and
    `8` is the least order at which a retraction fails (`Q₈`);
14. the `GL₂` obstruction is about the size of the matrices, not the ring: it persists in every
    even size, while over `𝔽₅` and over `ℝ` the odd-size group `GL₃` does retract.
-/

open Subgroup

/-- **Atlas of the center-retraction half of the project.**  A single conjunction gathering the
positive families, the two structural criteria, the obstructions, and the classifications for
the dihedral and dicyclic families. -/
theorem centerRetractionAtlas :
    -- 1. abelian groups
    (∀ (G : Type) [CommGroup G], HasCenterRetraction G) ∧
    -- 2. centerless groups
    (∀ (G : Type) [Group G], center G = ⊥ → HasCenterRetraction G) ∧
    -- 3. the complement criterion
    (∀ (G : Type) [Group G],
      HasCenterRetraction G ↔ ∃ N : Subgroup G, IsComplement' N (center G)) ∧
    -- 4. the splitting criterion
    (∀ (G : Type) [Group G],
      HasCenterRetraction G ↔
        ∃ N : Subgroup G, center N = ⊥ ∧ Nonempty (G ≃* (N × center G))) ∧
    -- 5. the nilpotent obstruction
    (∀ (G : Type) [Group G] [Group.IsNilpotent G],
      (¬ ∀ a b : G, a * b = b * a) → ¬ HasCenterRetraction G) ∧
    -- 6. the Schur–Zassenhaus criterion
    (∀ (G : Type) [Group G],
      (Nat.card (center G)).Coprime (center G).index → HasCenterRetraction G) ∧
    -- 7. binary products
    (∀ (G H : Type) [Group G] [Group H],
      HasCenterRetraction (G × H) ↔ HasCenterRetraction G ∧ HasCenterRetraction H) ∧
    -- 8. arbitrary products
    (∀ (ι : Type) [DecidableEq ι] (G : ι → Type) [∀ i, Group (G i)],
      HasCenterRetraction (∀ i, G i) ↔ ∀ i, HasCenterRetraction (G i)) ∧
    -- 9. the dihedral family
    (∀ n : ℕ, HasCenterRetraction (DihedralGroup n) ↔ (n = 0 ∨ ¬ (4 ∣ n))) ∧
    -- 10. the dicyclic family
    (∀ n : ℕ, HasCenterRetraction (QuaternionGroup n) ↔ n < 2) ∧
    -- 11. symmetric, alternating, and general linear groups
    ((∀ n : ℕ, HasCenterRetraction (Equiv.Perm (Fin n))) ∧
      (∀ n : ℕ, HasCenterRetraction (alternatingGroup (Fin n))) ∧
      (∀ (R : Type) [CommRing R], (2 : R) ≠ 0 →
        ¬ HasCenterRetraction (Matrix (Fin 2) (Fin 2) R)ˣ)) ∧
    -- 12. sharpness of the commutator obstruction, and failure of heredity
    ((∀ (G : Type) [Group G], HasCenterRetraction G →
        Disjoint (commutator G) (center G)) ∧
      (Disjoint (commutator (QuaternionGroup 3)) (center (QuaternionGroup 3)) ∧
        Nontrivial (center (QuaternionGroup 3)) ∧
        ¬ HasCenterRetraction (QuaternionGroup 3)) ∧
      (HasCenterRetraction (Equiv.Perm (QuaternionGroup 2)) ∧
        ¬ HasCenterRetraction CenterRetractionHeredity.cayleyImage) ∧
      (HasCenterRetraction (DihedralGroup 0) ∧
        ¬ HasCenterRetraction
          (DihedralGroup 0 ⧸ (CenterRetractionHeredity.dihedralProj 4).ker))) ∧
    -- 13. squarefree orders, and the least order at which a retraction fails
    ((∀ (G : Type) [Group G] [Finite G], Squarefree (Nat.card G) → HasCenterRetraction G) ∧
      (∀ (G : Type) [Group G] [Finite G], Nat.card G < 8 → HasCenterRetraction G) ∧
      Nat.card (QuaternionGroup 2) = 8 ∧ ¬ HasCenterRetraction (QuaternionGroup 2)) ∧
    -- 14. `GL₂` versus `GL₃`
    ((¬ HasCenterRetraction (GL (Fin 2) (ZMod 5)) ∧
        HasCenterRetraction (GL (Fin 3) (ZMod 5))) ∧
      (¬ HasCenterRetraction (GL (Fin 2) ℝ) ∧ HasCenterRetraction (GL (Fin 3) ℝ)) ∧
      (∀ m : ℕ, m ≠ 0 →
        ¬ HasCenterRetraction (Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ)ˣ)) := by
  refine ⟨fun G _ => hasCenterRetraction_of_commGroup G,
    fun G _ h => hasCenterRetraction_of_center_eq_bot h,
    fun G _ => hasCenterRetraction_iff_isComplement G,
    fun G _ => hasCenterRetraction_iff_mulEquiv_prod,
    fun G _ _ h => not_hasCenterRetraction_of_nilpotent h,
    fun G _ h => hasCenterRetraction_of_coprime h,
    fun G H _ _ => hasCenterRetraction_prod_iff,
    fun ι _ G _ => hasCenterRetraction_pi_iff,
    fun n => DihedralGroup.hasCenterRetraction_dihedral_iff_all n,
    fun n => QuaternionGroup.hasCenterRetraction_quaternion_iff n,
    ⟨fun n => CenterRetractionPerm.hasCenterRetraction_perm_fin n,
      fun n => CenterRetractionPerm.hasCenterRetraction_alternatingGroup_fin n,
      fun R _ h2 => GL2.not_hasCenterRetraction (R := R) h2⟩,
    ⟨fun G _ h => ?_, disjoint_commutator_center_not_sufficient,
      CenterRetractionHeredity.hasCenterRetraction_not_hereditary_subgroup,
      CenterRetractionHeredity.hasCenterRetraction_not_hereditary_quotient⟩,
    ⟨fun _ _ _ h => CenterRetractionSmall.hasCenterRetraction_of_squarefree_card h,
      fun _ _ _ h => CenterRetractionSmall.hasCenterRetraction_of_card_lt_eight h,
      CenterRetractionSmall.card_quaternionGroup_two, not_hasCenterRetraction_quaternion⟩,
    ⟨generalLinear_obstruction_depends_on_size.1, generalLinear_obstruction_depends_on_size.2,
      fun m hm => GLEven.not_hasCenterRetraction_even hm (by norm_num)⟩⟩
  obtain ⟨r, hr⟩ := h
  exact disjoint_commutator_center hr
