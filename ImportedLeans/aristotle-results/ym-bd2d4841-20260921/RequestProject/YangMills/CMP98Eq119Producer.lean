/-
# The strongest Eq. (119) producer: no caller-chosen data downstream of the
physical lattice fields

The layers `CMP98Eq119Transport`, `CMP98Eq119GCalculus`, `CMP98Eq119Assembly`
and `CMP98Eq119PhysicalLog` still let a caller *choose* several objects that
Bałaban's text actually constructs: the averaging contours, the coarse bond,
the pointwise Lie elements `Y_x`, the outer `Y`, and the two trivialisation
inverses `J∓`.  This file removes all of that freedom.

The only inputs of `eq119Physical` are

* the periodic link field `U`,
* the perturbation one-form `A`,
* the block centre `c₋`, and
* the coarse **axis** and **orientation**.

Everything else is constructed from those:

* the coarse bond is the canonical straight signed segment of length `13`
  (`coarseBond`), and the centre-to-point legs are the canonical axial words
  (`legWord`) — so `x ↦ x'` is not data (`physicalContour_endpoint`);
* `Y_x` is the logarithm of the literal relative contour element
  `U(Γ_{c,x}) · U(c)^{-1}` (`physicalYAt`);
* the outer `Y` is their block average `13^{-4} Σ_x Y_x`
  (`physicalYOuter_eq_blockAverage`), not an independent choice;
* the trivialisations are `g(±ad Y_x)` and their inverses are taken with
  `Ring.inverse`, which the small-field hypothesis turns into genuine two-sided
  inverses (`physicalJMinus_mul`, `physicalJPlus_mul`).

`eq119Physical_from_lattice_data` collects this: a single `ε > 0` such that for
*every* link field, one-form, centre, axis and orientation satisfying the
small-field condition, all of the above hold simultaneously, and the two
printed spellings of Eq. (119) agree.

**Honest status.** This is still the algebraic/geometric/Lie-calculus layer of
Eq. (119).  Identifying these objects with the literal fields, contours and
constants of the Bałaban papers, and every analytic estimate downstream of
Eq. (119), is neither done nor claimed here.
-/
import RequestProject.YangMills.CMP98Eq119PhysicalLog

namespace YangMills.CMP98Eq119

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [Nontrivial A]
variable {N : ℕ}

/-! ## 1. The constructed data -/

/-- The literal Eq. (119) averaging contour at a block offset: the canonical
centre-to-point leg, the canonical coarse bond, and the reversed leg. -/
def physicalContour (μ : Fin 4) (o : Bool) (p : BlockOffset) : List (Step 4) :=
  eq119Contour legWord (coarseBond μ o) p

/-- Bałaban's pointwise Lie element `Y_x`: the logarithm of the literal
relative contour element `U(Γ_{c,x}) · U(c)^{-1}`. -/
noncomputable def physicalYAt (link : PSite 4 N → Step 4 → Aˣ) (cMinus : PSite 4 N)
    (μ : Fin 4) (o : Bool) (p : BlockOffset) : A :=
  physicalLog link cMinus (physicalContour μ o p) (coarseBond μ o)

/-- The outer Lie element `Y = 13^{-4} Σ_x Y_x`, constructed rather than
chosen. -/
noncomputable def physicalYOuter (link : PSite 4 N → Step 4 → Aˣ) (cMinus : PSite 4 N)
    (μ : Fin 4) (o : Bool) : A :=
  blockAverage (physicalYAt link cMinus μ o)

/-- The pointwise trivialisation inverse `g^{-1}(ad Y_x)`. -/
noncomputable def physicalJMinus (link : PSite 4 N → Step 4 → Aˣ) (cMinus : PSite 4 N)
    (μ : Fin 4) (o : Bool) (p : BlockOffset) : A →L[ℝ] A :=
  Ring.inverse (balabanG (adOp (physicalYAt link cMinus μ o p)))

/-- The opposite pointwise trivialisation inverse `g^{-1}(−ad Y_x)`. -/
noncomputable def physicalJPlus (link : PSite 4 N → Step 4 → Aˣ) (cMinus : PSite 4 N)
    (μ : Fin 4) (o : Bool) (p : BlockOffset) : A →L[ℝ] A :=
  Ring.inverse (balabanG (-(adOp (physicalYAt link cMinus μ o p))))

/-- **The Eq. (119) one-step averaging derivative, produced from the lattice
data alone.**  Its arguments are the link field, the one-form, the block
centre, and the coarse axis and orientation — nothing else. -/
noncomputable def eq119Physical (link : PSite 4 N → Step 4 → Aˣ)
    (Afield : PSite 4 N → Step 4 → A) (cMinus : PSite 4 N) (μ : Fin 4) (o : Bool) : A :=
  eq119 link Afield (physicalYAt link cMinus μ o) (physicalJMinus link cMinus μ o)
    legWord (coarseBond μ o) cMinus

/-! ## 2. The geometry is a computation, not a receipt -/

/-- Every one of the `13⁴ = 28561` constructed contours joins the block centre
to the canonical neighbouring centre.  No `x ↦ x'` datum is consumed. -/
theorem physicalContour_endpoint (cMinus : PSite 4 N) (μ : Fin 4) (o : Bool)
    (p : BlockOffset) :
    walk cMinus (physicalContour μ o p) = nextCentre cMinus μ o :=
  eq119Contour_endpoint (fun q => walk_legWord cMinus q) (walk_coarseBond cMinus μ o) p

omit [Nontrivial A] in
/-- The outer Lie element really is the block average of the pointwise ones. -/
theorem physicalYOuter_eq_blockAverage (link : PSite 4 N → Step 4 → Aˣ)
    (cMinus : PSite 4 N) (μ : Fin 4) (o : Bool) :
    physicalYOuter link cMinus μ o = blockAverage (physicalYAt link cMinus μ o) := rfl

/-! ## 3. The trivialisation inverses are produced -/

theorem physicalJMinus_mul {link : PSite 4 N → Step 4 → Aˣ} {cMinus : PSite 4 N}
    {μ : Fin 4} {o : Bool} {p : BlockOffset}
    (h : ‖physicalYAt link cMinus μ o p‖ < Real.log 2 / 2) :
    balabanG (adOp (physicalYAt link cMinus μ o p)) * physicalJMinus link cMinus μ o p = 1 :=
  Ring.mul_inverse_cancel _ (exists_inverse_of_norm_lt h).1

theorem physicalJPlus_mul {link : PSite 4 N → Step 4 → Aˣ} {cMinus : PSite 4 N}
    {μ : Fin 4} {o : Bool} {p : BlockOffset}
    (h : ‖physicalYAt link cMinus μ o p‖ < Real.log 2 / 2) :
    physicalJPlus link cMinus μ o p * balabanG (-(adOp (physicalYAt link cMinus μ o p))) = 1 :=
  Ring.inverse_mul_cancel _ (exists_inverse_of_norm_lt h).2

/-! ## 4. The small-field hypothesis, and the capstone -/

/-- The small-field condition at the block: every constructed relative contour
element is close to the identity, and every `Y_x` is small enough for the
trivialisations to be invertible. -/
def PhysicalSmallField (ε : ℝ) (link : PSite 4 N → Step 4 → Aˣ) (cMinus : PSite 4 N)
    (μ : Fin 4) (o : Bool) : Prop :=
  (∀ p, ‖relativeHolonomy link cMinus (physicalContour μ o p) (coarseBond μ o) - 1‖ < ε)
    ∧ (∀ p, ‖physicalYAt link cMinus μ o p‖ < Real.log 2 / 2)

/-- **Everything Eq. (119) needs is derived from the physical lattice data.**
There is one radius `ε > 0` such that for every link field, one-form, block
centre, coarse axis and orientation in the small-field regime:

1. all `13⁴` constructed contours join the two block centres;
2. `exp Y_x` really is the literal relative contour element;
3. the outer `Y` is the block average of the `Y_x`;
4. `g(ad Y_x)` and `g(−ad Y_x)` are inverted by the constructed `J∓`;
5. the two printed spellings of Eq. (119) give the *same* operator.

None of `Y_x`, `Y`, `log`, `g`, `g^{-1}`, `J∓`, the legs, the coarse bond, its
length, or the point matching `x ↦ x'` is caller-supplied. -/
theorem eq119Physical_from_lattice_data :
    ∃ ε > 0, ∀ (link : PSite 4 N → Step 4 → Aˣ) (Afield : PSite 4 N → Step 4 → A)
      (cMinus : PSite 4 N) (μ : Fin 4) (o : Bool),
      PhysicalSmallField (A := A) ε link cMinus μ o →
      (∀ p, walk cMinus (physicalContour μ o p) = nextCentre cMinus μ o) ∧
      (∀ p, NormedSpace.exp (physicalYAt link cMinus μ o p)
          = relativeHolonomy link cMinus (physicalContour μ o p) (coarseBond μ o)) ∧
      physicalYOuter link cMinus μ o = blockAverage (physicalYAt link cMinus μ o) ∧
      (∀ p, balabanG (adOp (physicalYAt link cMinus μ o p))
          * physicalJMinus link cMinus μ o p = 1) ∧
      (∀ p, physicalJPlus link cMinus μ o p
          * balabanG (-(adOp (physicalYAt link cMinus μ o p))) = 1) ∧
      eq119Physical link Afield cMinus μ o
        = blockAverage (fun p =>
            balabanG (-(adOp (physicalYOuter link cMinus μ o)))
              (physicalJPlus link cMinus μ o p
                (NormedSpace.exp (physicalYAt link cMinus μ o p)
                  * rzero link adjHom Afield cMinus (physicalContour μ o p)
                  * NormedSpace.exp (-(physicalYAt link cMinus μ o p))))) := by
  obtain ⟨ε, hε, hexp⟩ := exists_exp_physicalLog (A := A) (N := N)
  refine ⟨ε, hε, fun link Afield cMinus μ o hsmall => ?_⟩
  obtain ⟨hclose, hnorm⟩ := hsmall
  refine ⟨fun p => physicalContour_endpoint cMinus μ o p,
    fun p => hexp _ _ _ _ (hclose p), rfl,
    fun p => physicalJMinus_mul (hnorm p), fun p => physicalJPlus_mul (hnorm p), ?_⟩
  exact eq119_of_plus_convention link Afield (physicalYAt link cMinus μ o)
    (physicalJMinus link cMinus μ o) (physicalJPlus link cMinus μ o) legWord
    (coarseBond μ o) cMinus (fun p => physicalJMinus_mul (hnorm p))
    (fun p => physicalJPlus_mul (hnorm p))

end YangMills.CMP98Eq119
