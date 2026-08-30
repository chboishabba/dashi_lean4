import RequestProject.CenterRetraction
import RequestProject.CenterRetractionMore
import RequestProject.CenterRetractionProd
import RequestProject.CenterRetractionPerm
import RequestProject.QuaternionCenterRetraction
import RequestProject.DihedralCenterRetraction
import RequestProject.DihedralInfinite

/-!
# How badly does `HasCenterRetraction` fail to be hereditary?

The earlier files establish that retracting onto the center is invariant under isomorphism
(`hasCenterRetraction_congr`) and is inherited by *direct factors*
(`hasCenterRetraction_prod_iff`, `hasCenterRetraction_pi_iff`).  This file shows that these
are essentially the only stability properties available: the class is closed under **neither
subgroups nor quotients**, and it always forces a splitting of the abelianization.

* `abelianization_of_center_injective`, `exists_abelianization_center_retraction` : a retraction
  `G →* Z(G)` automatically factors through `Gᵃᵇ`, so the center embeds in the abelianization
  as a direct factor.
* `not_hasCenterRetraction_cayleyImage` / `hasCenterRetraction_not_hereditary_subgroup` : the
  symmetric group `S₈ = Perm Q₈` is centerless, hence retracts onto its center, yet its Cayley
  copy of the quaternion group `Q₈` does not.  So the property does not pass to subgroups.
* `dihedralProj`, `not_hasCenterRetraction_quotient_dihedral` : the infinite dihedral group
  `D∞` is centerless, hence retracts onto its center, yet its quotient by the kernel of the
  reduction `D∞ ↠ D₄` is `D₄`, which does not.  So the property does not pass to quotients.
-/

open Subgroup

namespace CenterRetractionHeredity

section Abelianization

variable {G : Type*} [Group G]

/-- A retraction onto the center factors through the abelianization: there is
`φ : Gᵃᵇ →* Z(G)` restricting to the identity on (the image of) the center. -/
theorem exists_abelianization_center_retraction (h : HasCenterRetraction G) :
    ∃ φ : Abelianization G →* center G, ∀ z : center G, φ (Abelianization.of (z : G)) = z := by
  obtain ⟨r, hr⟩ := h
  exact ⟨Abelianization.lift r, fun z => by simpa using hr z⟩

/-- **The center embeds in the abelianization** as soon as `G` retracts onto its center.
(For a general group the composite `Z(G) → G → Gᵃᵇ` can kill the whole center — e.g. for `Q₈`.) -/
theorem abelianization_of_center_injective (h : HasCenterRetraction G) :
    Function.Injective (Abelianization.of.comp (center G).subtype) := by
  obtain ⟨φ, hφ⟩ := exists_abelianization_center_retraction h
  intro a b hab
  have : φ (Abelianization.of (a : G)) = φ (Abelianization.of (b : G)) := by
    simpa using congrArg φ hab
  rwa [hφ a, hφ b] at this

/-- **A numerical obstruction.**  If a finite group retracts onto its center, then the order of
the center divides the order of the abelianization. -/
theorem card_center_dvd_card_abelianization [Finite G] (h : HasCenterRetraction G) :
    Nat.card (center G) ∣ Nat.card (Abelianization G) :=
  Subgroup.card_dvd_of_injective (Abelianization.of.comp (center G).subtype)
    (abelianization_of_center_injective h)

end Abelianization

section Subgroups

/-- The Cayley copy of `Q₈` inside the symmetric group on its own eight elements. -/
def cayleyImage : Subgroup (Equiv.Perm (QuaternionGroup 2)) :=
  (MulAction.toPermHom (QuaternionGroup 2) (QuaternionGroup 2)).range

/-- The Cayley copy of `Q₈` is isomorphic to `Q₈`. -/
noncomputable def cayleyEquiv : QuaternionGroup 2 ≃* cayleyImage :=
  Equiv.Perm.subgroupOfMulAction (QuaternionGroup 2) (QuaternionGroup 2)

/-- The Cayley copy of `Q₈` inside `S₈` does **not** retract onto its center. -/
theorem not_hasCenterRetraction_cayleyImage : ¬ HasCenterRetraction cayleyImage := by
  intro h
  exact not_hasCenterRetraction_quaternion (hasCenterRetraction_congr cayleyEquiv.symm h)

/-- The ambient symmetric group `S₈ = Perm Q₈` does retract onto its center (it is centerless). -/
theorem hasCenterRetraction_perm_quaternion :
    HasCenterRetraction (Equiv.Perm (QuaternionGroup 2)) :=
  CenterRetractionPerm.hasCenterRetraction_perm

/-- **Retracting onto the center is not inherited by subgroups**: `Perm Q₈` retracts onto its
center, but its subgroup `cayleyImage ≅ Q₈` does not. -/
theorem hasCenterRetraction_not_hereditary_subgroup :
    HasCenterRetraction (Equiv.Perm (QuaternionGroup 2)) ∧
      ¬ HasCenterRetraction cayleyImage :=
  ⟨hasCenterRetraction_perm_quaternion, not_hasCenterRetraction_cayleyImage⟩

end Subgroups

section Quotients

/-- Reduction of the rotation exponent modulo `n`, as a map on underlying types. -/
def dihedralProjFun (n : ℕ) : DihedralGroup 0 → DihedralGroup n
  | .r i => .r (Int.cast i)
  | .sr i => .sr (Int.cast i)

/-- **The reduction homomorphism `D∞ ↠ D_n`**, sending `r^k ↦ r^(k mod n)` and
`s r^k ↦ s r^(k mod n)`. -/
def dihedralProj (n : ℕ) : DihedralGroup 0 →* DihedralGroup n where
  toFun := dihedralProjFun n
  map_one' := by
    show dihedralProjFun n (DihedralGroup.r 0) = DihedralGroup.r 0
    simp [dihedralProjFun]
  map_mul' := by
    rintro (i | i) (j | j) <;>
      simp only [dihedralProjFun, DihedralGroup.r_mul_r, DihedralGroup.r_mul_sr,
        DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr, DihedralGroup.r.injEq,
        DihedralGroup.sr.injEq] <;>
      first
        | exact Int.cast_add (R := ZMod n) i j
        | exact Int.cast_sub (R := ZMod n) j i

theorem dihedralProj_surjective (n : ℕ) : Function.Surjective (dihedralProj n) := by
  rintro (i | i)
  · obtain ⟨k, hk⟩ := ZMod.intCast_surjective (n := n) i
    exact ⟨DihedralGroup.r k, by show DihedralGroup.r (Int.cast k) = _; rw [hk]⟩
  · obtain ⟨k, hk⟩ := ZMod.intCast_surjective (n := n) i
    exact ⟨DihedralGroup.sr k, by show DihedralGroup.sr (Int.cast k) = _; rw [hk]⟩

/-- The quotient of `D∞` by the kernel of the reduction `D∞ ↠ D₄` is `D₄`. -/
noncomputable def quotientEquivDihedralFour :
    (DihedralGroup 0 ⧸ (dihedralProj 4).ker) ≃* DihedralGroup 4 :=
  QuotientGroup.quotientKerEquivOfSurjective _ (dihedralProj_surjective 4)

/-- **Retracting onto the center is not inherited by quotients**: the infinite dihedral group
is centerless (so it retracts onto its center), but the quotient realizing `D₄` does not. -/
theorem not_hasCenterRetraction_quotient_dihedral :
    ¬ HasCenterRetraction (DihedralGroup 0 ⧸ (dihedralProj 4).ker) := by
  intro h
  exact not_hasCenterRetraction_dihedral_four
    (hasCenterRetraction_congr quotientEquivDihedralFour h)

/-- Packaged statement: a group retracting onto its center with a quotient that does not. -/
theorem hasCenterRetraction_not_hereditary_quotient :
    HasCenterRetraction (DihedralGroup 0) ∧
      ¬ HasCenterRetraction (DihedralGroup 0 ⧸ (dihedralProj 4).ker) :=
  ⟨DihedralGroup.hasCenterRetraction_zero, not_hasCenterRetraction_quotient_dihedral⟩

end Quotients

end CenterRetractionHeredity
