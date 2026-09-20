import Synthesis.MillenniumBSDLocalKummerHomomorphism
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Tactic

/-!
# The local Kummer map factors through E(Q_p) / 2E(Q_p)

The previous tranche proves the total local two-descent map

  delta_p : E(Q_p) -> (Q_p^*/Q_p^{*2})^2

is multiplicative with respect to the genuine elliptic group law. Since the
domain is written additively and the square-class target multiplicatively, we
package it as a MonoidHom out of Multiplicative E(Q_p).

The target has exponent two, so every double maps to one. Hence delta_p kills
the subgroup 2E(Q_p) and descends to the literal quotient E(Q_p)/2E(Q_p).
-/

namespace Synthesis.Millennium.BSD

noncomputable def totalLocalKummerMonoidHom
    (p : ℕ) [Fact p.Prime] :
    Multiplicative (PadicProjectivePoint p) →*
      (PadicSquareClass p × PadicSquareClass p) where
  toFun P := totalLocalKummer p P.toAdd
  map_one' := by
    simpa using totalLocalKummer_zero p
  map_mul' := by
    intro P Q
    change
      totalLocalKummer p (P.toAdd + Q.toAdd)
        =
      totalLocalKummer p P.toAdd *
        totalLocalKummer p Q.toAdd
    exact totalLocalKummer_homomorphism p P.toAdd Q.toAdd

@[simp] theorem totalLocalKummerMonoidHom_apply
    (p : ℕ) [Fact p.Prime]
    (P : PadicProjectivePoint p) :
    totalLocalKummerMonoidHom p (Multiplicative.ofAdd P)
      =
    totalLocalKummer p P :=
  rfl

theorem totalLocalKummerMonoidHom_range_eq
    (p : ℕ) [Fact p.Prime] :
    (totalLocalKummerMonoidHom p).range
      =
    localKummerImageSubgroup p := by
  ext a
  constructor
  · rintro ⟨P, rfl⟩
    exact ⟨P.toAdd, rfl⟩
  · rintro ⟨P, rfl⟩
    exact ⟨Multiplicative.ofAdd P, rfl⟩

theorem totalLocalKummer_double_eq_one
    (p : ℕ) [Fact p.Prime]
    (P : PadicProjectivePoint p) :
    totalLocalKummer p (P + P) = 1 := by
  rw [totalLocalKummer_homomorphism]
  apply Prod.ext
  · exact padicSquareClass_sq_eq_one p
      (totalLocalKummer p P).1
  · exact padicSquareClass_sq_eq_one p
      (totalLocalKummer p P).2

def localDoubleSubgroup
    (p : ℕ) [Fact p.Prime] :
    Subgroup (Multiplicative (PadicProjectivePoint p)) where
  carrier := {x | ∃ P : PadicProjectivePoint p, x.toAdd = P + P}
  one_mem' := by
    refine ⟨0, ?_⟩
    simp
  mul_mem' := by
    intro x y hx hy
    rcases hx with ⟨P, hP⟩
    rcases hy with ⟨Q, hQ⟩
    refine ⟨P + Q, ?_⟩
    simp only [Multiplicative.toAdd_mul]
    rw [hP, hQ]
    abel
  inv_mem' := by
    intro x hx
    rcases hx with ⟨P, hP⟩
    refine ⟨-P, ?_⟩
    simp only [Multiplicative.toAdd_inv]
    rw [hP]
    abel

theorem localDoubleSubgroup_le_kummerKernel
    (p : ℕ) [Fact p.Prime] :
    localDoubleSubgroup p
      ≤
    (totalLocalKummerMonoidHom p).ker := by
  intro x hx
  rcases hx with ⟨P, hP⟩
  change totalLocalKummer p x.toAdd = 1
  rw [hP]
  exact totalLocalKummer_double_eq_one p P

noncomputable def localKummerQuotientHom
    (p : ℕ) [Fact p.Prime] :
    (Multiplicative (PadicProjectivePoint p) ⧸ localDoubleSubgroup p) →*
      (PadicSquareClass p × PadicSquareClass p) :=
  QuotientGroup.lift
    (localDoubleSubgroup p)
    (totalLocalKummerMonoidHom p)
    (localDoubleSubgroup_le_kummerKernel p)

@[simp] theorem localKummerQuotientHom_mk
    (p : ℕ) [Fact p.Prime]
    (P : PadicProjectivePoint p) :
    localKummerQuotientHom p
      (QuotientGroup.mk'
        (localDoubleSubgroup p)
        (Multiplicative.ofAdd P))
      =
    totalLocalKummer p P := by
  rfl

theorem localKummerQuotientHom_range_eq
    (p : ℕ) [Fact p.Prime] :
    (localKummerQuotientHom p).range
      =
    localKummerImageSubgroup p := by
  rw [← totalLocalKummerMonoidHom_range_eq p]
  ext a
  constructor
  · rintro ⟨q, rfl⟩
    refine QuotientGroup.induction_on q ?_
    intro P
    exact ⟨P, rfl⟩
  · rintro ⟨P, rfl⟩
    exact
      ⟨QuotientGroup.mk'
          (localDoubleSubgroup p) P, rfl⟩

noncomputable def localKummerQuotientToImage
    (p : ℕ) [Fact p.Prime] :
    (Multiplicative (PadicProjectivePoint p) ⧸ localDoubleSubgroup p) →*
      localKummerImageSubgroup p :=
  (localKummerQuotientHom p).codRestrict
    (localKummerImageSubgroup p)
    (fun q => by
      have h :
          localKummerQuotientHom p q ∈
            (localKummerQuotientHom p).range :=
        ⟨q, rfl⟩
      rwa [localKummerQuotientHom_range_eq p] at h)

theorem localKummerQuotientToImage_surjective
    (p : ℕ) [Fact p.Prime] :
    Function.Surjective (localKummerQuotientToImage p) := by
  intro y
  rcases y with ⟨y, hy⟩
  have hyrange :
      y ∈ (localKummerQuotientHom p).range := by
    rwa [localKummerQuotientHom_range_eq p]
  rcases hyrange with ⟨q, hq⟩
  refine ⟨q, ?_⟩
  apply Subtype.ext
  exact hq

theorem localKummerImage_is_quotient_image
    (p : ℕ) [Fact p.Prime] :
    ∀ y : localKummerImageSubgroup p,
      ∃ q :
        Multiplicative (PadicProjectivePoint p) ⧸ localDoubleSubgroup p,
        localKummerQuotientToImage p q = y :=
  localKummerQuotientToImage_surjective p

end Synthesis.Millennium.BSD
