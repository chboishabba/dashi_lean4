/-
# The one-step averaging derivative of CMP 98 Eq. (119), assembled

This file joins the two machine-checked layers

* `CMP98Eq119Transport` — signed-bond contours, holonomy, the transported
  one-form `R₀A`, and the block average, and
* `CMP98Eq119GCalculus` — Bałaban's `g`, the identity `g(−x) = e^x g(x)`, the
  inverse transport, and small-field invertibility,

into the object the source writes at Eq. (119), with the adjoint action taken
to be honest conjugation rather than an abstract slot.

Proved here:

* `expAd_apply` — `exp(ad Y) z = e^{Y} z e^{−Y}`: the exponential of the
  commutator operator **is** the adjoint action of the exponentiated element.
  Proved from the commuting left/right multiplication algebra homomorphisms, so
  no `Ad`/`exp` compatibility has to be assumed.
* `balabanG_adOp_neg_apply` — consequently `g(−ad Y) = Ad_{e^{Y}} ∘ g(ad Y)`:
  the left/right trivialisation relation of the source, with a genuine adjoint.
* `eq119Contour_endpoint` — the literal averaging contour
  `Γ(p) = leg(p) ⌢ crossing ⌢ leg(p)^{-1}` joins the two block centres for
  **every** one of the `13⁴ = 28561` block points, derived from a *single*
  centre-to-centre crossing word plus periodic translation covariance.
* `eq119` — the Eq. (119)-shaped one-step derivative: the block average over
  the `28561` points of `g(−ad Y)·J(x)·R₀A(Γ(x))`, in which the outer Lie
  element `Y` is *constructed* as the block average `L^{-d} Σ_x Y_x` rather
  than chosen.
* `eq119Summand_transport` — the two opposite spellings of the pointwise
  trivialisation agree: `J₊(x) ∘ Ad_{e^{Y_x}} = J₋(x)`.  A later adapter
  therefore cannot silently flip the convention.
* `exists_inverse_of_norm_lt` — in the small-field regime `‖Y_x‖ < ½ log 2`
  the pointwise inverses used above exist; they are produced from
  `‖ad Y‖ ≤ 2‖Y‖` and the small-field criterion, not assumed.

**Honest status.** This is the algebraic/geometric layer of Eq. (119) and its
Lie calculus.  Identifying these objects with the literal fields, contours and
constants of the Bałaban papers, and every analytic estimate downstream of
Eq. (119), is *not* done here and is not claimed.
-/
import RequestProject.YangMills.CMP98Eq119Transport
import RequestProject.YangMills.CMP98Eq119GCalculus

namespace YangMills.CMP98Eq119

open ContinuousLinearMap

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

/-! ## 1. Left/right multiplication and the commutator operator `ad` -/

/-- Left multiplication as a continuous algebra homomorphism. -/
noncomputable def lmulA : A →ₐ[ℝ] (A →L[ℝ] A) where
  toFun a := ContinuousLinearMap.mul ℝ A a
  map_one' := by ext z; simp
  map_mul' a b := by ext z; simp [mul_assoc]
  map_zero' := by ext z; simp
  map_add' a b := by ext z; simp
  commutes' r := by ext z; simp [Algebra.smul_def]

/-- Right multiplication as a continuous algebra homomorphism from the
opposite algebra. -/
noncomputable def rmulA : Aᵐᵒᵖ →ₐ[ℝ] (A →L[ℝ] A) where
  toFun a := (ContinuousLinearMap.mul ℝ A).flip a.unop
  map_one' := by ext z; simp
  map_mul' a b := by ext z; simp [mul_assoc]
  map_zero' := by ext z; simp
  map_add' a b := by ext z; simp
  commutes' r := by ext z; simp [Algebra.smul_def, Algebra.commutes]

@[simp] theorem lmulA_apply (a z : A) : lmulA a z = a * z := rfl

@[simp] theorem rmulA_apply (a : Aᵐᵒᵖ) (z : A) : rmulA a z = z * a.unop := rfl

/-- The adjoint (commutator) operator `ad Y = [Y, ·]`. -/
noncomputable def adOp (Y : A) : A →L[ℝ] A := lmulA Y - rmulA (MulOpposite.op Y)

@[simp] theorem adOp_apply (Y z : A) : adOp Y z = Y * z - z * Y := rfl

theorem norm_adOp_le (Y : A) : ‖adOp Y‖ ≤ 2 * ‖Y‖ := by
  have h1 : ‖(lmulA Y : A →L[ℝ] A)‖ ≤ ‖Y‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (fun z => ?_)
    exact norm_mul_le _ _
  have h2 : ‖(rmulA (MulOpposite.op Y) : A →L[ℝ] A)‖ ≤ ‖Y‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (fun z => ?_)
    calc ‖z * Y‖ ≤ ‖z‖ * ‖Y‖ := norm_mul_le _ _
      _ = ‖Y‖ * ‖z‖ := by ring
  calc ‖adOp Y‖ ≤ ‖(lmulA Y : A →L[ℝ] A)‖ + ‖(rmulA (MulOpposite.op Y) : A →L[ℝ] A)‖ :=
        norm_sub_le _ _
    _ ≤ ‖Y‖ + ‖Y‖ := add_le_add h1 h2
    _ = 2 * ‖Y‖ := by ring

theorem commute_lmulA_rmulA (Y : A) :
    Commute (lmulA Y : A →L[ℝ] A) (rmulA (MulOpposite.op Y)) := by
  ext z
  simp [ContinuousLinearMap.mul_apply, mul_assoc]

/-! ## 2. The adjoint action of the gauge group on the Lie algebra -/

/-- `Ad : Aˣ → End(A)`, `Ad u z = u z u⁻¹` — the transport used by `R₀A`. -/
noncomputable def adjHom : Aˣ →* Module.End ℝ A where
  toFun u :=
    { toFun := fun z => (u : A) * z * ((u⁻¹ : Aˣ) : A)
      map_add' := by intro a b; simp [mul_add, add_mul]
      map_smul' := by intro r a; simp }
  map_one' := by ext z; simp
  map_mul' u v := by ext z; simp [mul_assoc]

@[simp] theorem adjHom_apply (u : Aˣ) (z : A) :
    adjHom u z = (u : A) * z * ((u⁻¹ : Aˣ) : A) := rfl

/-! ## 3. The literal averaging contour and its endpoints -/

/-- The one-step averaging contour of the source: the centre-to-point leg, the
crossing bond, and the reversed leg of the neighbouring block. -/
def eq119Contour (leg : BlockOffset → List (Step 4)) (cross : List (Step 4))
    (p : BlockOffset) : List (Step 4) :=
  leg p ++ cross ++ revWord (leg p)

/-- Every one of the `13⁴ = 28561` averaging contours joins the two block
centres, from a *single* centre-to-centre crossing word. -/
theorem eq119Contour_endpoint {N : ℕ} {cMinus cPlus : PSite 4 N}
    {leg : BlockOffset → List (Step 4)} {cross : List (Step 4)}
    (hleg : ∀ p, walk cMinus (leg p) = cMinus + embedOffset p)
    (hcross : walk cMinus cross = cPlus) (p : BlockOffset) :
    walk cMinus (eq119Contour leg cross p) = cPlus := by
  set q : PSite 4 N := embedOffset p with hq
  have hstep1 : walk cMinus (leg p) = cMinus + q := hleg p
  have hstep2 : walk (cMinus + q) cross = cPlus + q := crossing_of_centres hcross q
  have hback : walk (cPlus + q) (revWord (leg p)) = cPlus := by
    have hb0 : walk (walk cMinus (leg p)) (revWord (leg p)) = cMinus := walk_revWord _ _
    rw [hstep1] at hb0
    have hb1 : walk (cMinus + q + (cPlus - cMinus)) (revWord (leg p))
        = cMinus + (cPlus - cMinus) := by
      rw [walk_add, hb0]
    have hsimp : cMinus + q + (cPlus - cMinus) = cPlus + q := by abel
    have hsimp' : cMinus + (cPlus - cMinus) = cPlus := by abel
    rwa [hsimp, hsimp'] at hb1
  rw [eq119Contour, walk_append, walk_append, hstep1, hstep2, hback]

/-! ## 4. The exponential of `ad` -/

section Complete

variable [CompleteSpace A]

theorem lmulA_exp (Y : A) :
    (lmulA (NormedSpace.exp Y) : A →L[ℝ] A) = NormedSpace.exp (lmulA Y) := by
  refine NormedSpace.map_exp_of_mem_ball (𝕂 := ℝ) lmulA
    (ContinuousLinearMap.mul ℝ A).continuous Y ?_
  rw [NormedSpace.expSeries_radius_eq_top ℝ A]
  exact edist_lt_top _ _

theorem rmulA_exp (y : Aᵐᵒᵖ) :
    (rmulA (NormedSpace.exp y) : A →L[ℝ] A) = NormedSpace.exp (rmulA y) := by
  refine NormedSpace.map_exp_of_mem_ball (𝕂 := ℝ) rmulA ?_ y ?_
  · exact ((ContinuousLinearMap.mul ℝ A).flip).continuous.comp MulOpposite.continuous_unop
  · rw [NormedSpace.expSeries_radius_eq_top ℝ Aᵐᵒᵖ]
    exact edist_lt_top _ _

/-- **`exp(ad Y) = Ad_{exp Y}`**: the exponential of the commutator operator is
conjugation by the exponentiated element. -/
theorem expAd_apply (Y z : A) :
    NormedSpace.exp (adOp Y) z
      = NormedSpace.exp Y * z * NormedSpace.exp (-Y) := by
  have hcomm : Commute (lmulA Y : A →L[ℝ] A) (-(rmulA (MulOpposite.op Y))) :=
    (commute_lmulA_rmulA Y).neg_right
  have hsplit : NormedSpace.exp (adOp Y)
      = NormedSpace.exp (lmulA Y : A →L[ℝ] A)
        * NormedSpace.exp (-(rmulA (MulOpposite.op Y))) := by
    rw [adOp, sub_eq_add_neg]
    refine NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℝ) hcomm ?_ ?_ <;>
      · rw [NormedSpace.expSeries_radius_eq_top ℝ (A →L[ℝ] A)]
        exact edist_lt_top _ _
  have hneg : (-(rmulA (MulOpposite.op Y)) : A →L[ℝ] A)
      = rmulA (MulOpposite.op (-Y)) := by
    rw [MulOpposite.op_neg, map_neg]
  rw [hsplit, hneg, ← lmulA_exp, ← rmulA_exp, NormedSpace.exp_op]
  simp [ContinuousLinearMap.mul_apply, mul_assoc]


/-! ## 5. The Eq. (119) operator -/

section Nontrivial

variable [Nontrivial A]

/-- The left/right trivialisation relation with a genuine adjoint action:
`g(−ad Y) = Ad_{e^{Y}} ∘ g(ad Y)`. -/
theorem balabanG_adOp_neg_apply (Y z : A) :
    balabanG (-(adOp Y)) z
      = NormedSpace.exp Y * (balabanG (adOp Y) z) * NormedSpace.exp (-Y) := by
  rw [balabanG_neg, ContinuousLinearMap.mul_apply, expAd_apply]


/-- The Eq. (119) summand at one block point: the transported one-form along
the literal contour, hit by the pointwise inverse trivialisation and then by
the outer trivialisation `g(−ad Y)`, with `Y` the block average of the `Y_x`. -/
noncomputable def eq119Summand {N : ℕ}
    (link : PSite 4 N → Step 4 → Aˣ) (Afield : PSite 4 N → Step 4 → A)
    (Yp : BlockOffset → A) (J : BlockOffset → (A →L[ℝ] A))
    (leg : BlockOffset → List (Step 4)) (cross : List (Step 4))
    (cMinus : PSite 4 N) (p : BlockOffset) : A :=
  balabanG (-(adOp (blockAverage Yp)))
    (J p (rzero link adjHom Afield cMinus (eq119Contour leg cross p)))

/-- The Eq. (119) one-step averaging derivative: the `L^{-d}` block average of
the summands, `L^{-d} = 1/28561`. -/
noncomputable def eq119 {N : ℕ}
    (link : PSite 4 N → Step 4 → Aˣ) (Afield : PSite 4 N → Step 4 → A)
    (Yp : BlockOffset → A) (J : BlockOffset → (A →L[ℝ] A))
    (leg : BlockOffset → List (Step 4)) (cross : List (Step 4))
    (cMinus : PSite 4 N) : A :=
  blockAverage (eq119Summand link Afield Yp J leg cross cMinus)

/-- **The sign/convention transport at the Eq. (119) consumer.**  If `J₊(x)`
inverts `g(−ad Y_x)` and `J₋(x)` inverts `g(ad Y_x)`, then feeding `J₊(x)` the
adjoint-transported argument is the same as feeding `J₋(x)` the untransported
one.  The two spellings of Eq. (119) therefore agree. -/
theorem eq119Summand_transport {Yx : A} {Jm Jp : A →L[ℝ] A}
    (hm : balabanG (adOp Yx) * Jm = 1) (hp : Jp * balabanG (-(adOp Yx)) = 1) (z : A) :
    Jp (NormedSpace.exp Yx * z * NormedSpace.exp (-Yx)) = Jm z := by
  have h := balabanJ_transport hm hp
  have := congrArg (fun T : A →L[ℝ] A => T z) h
  simpa [ContinuousLinearMap.mul_apply, expAd_apply] using this

/-- The two spellings of Eq. (119) produce the *same* operator: replacing the
`g^{-1}(ad Y_x)` convention by the `g^{-1}(−ad Y_x)` one, with the adjoint
factor `Ad_{e^{Y_x}}` inserted where the source puts it, changes nothing. -/
theorem eq119_of_plus_convention {N : ℕ}
    (link : PSite 4 N → Step 4 → Aˣ) (Afield : PSite 4 N → Step 4 → A)
    (Yp : BlockOffset → A) (Jm Jp : BlockOffset → (A →L[ℝ] A))
    (leg : BlockOffset → List (Step 4)) (cross : List (Step 4)) (cMinus : PSite 4 N)
    (hm : ∀ p, balabanG (adOp (Yp p)) * Jm p = 1)
    (hp : ∀ p, Jp p * balabanG (-(adOp (Yp p))) = 1) :
    eq119 link Afield Yp Jm leg cross cMinus
      = blockAverage (fun p =>
          balabanG (-(adOp (blockAverage Yp)))
            (Jp p (NormedSpace.exp (Yp p)
                    * rzero link adjHom Afield cMinus (eq119Contour leg cross p)
                    * NormedSpace.exp (-(Yp p))))) := by
  unfold eq119 eq119Summand blockAverage
  congr 1
  refine Finset.sum_congr rfl (fun p _ => ?_)
  simp only [eq119Summand_transport (hm p) (hp p)]

/-- Small field ⇒ both pointwise trivialisations are invertible, so the
inverses consumed by Eq. (119) are produced rather than assumed. -/
theorem exists_inverse_of_norm_lt {Y : A} (hY : ‖Y‖ < Real.log 2 / 2) :
    IsUnit (balabanG (adOp Y)) ∧ IsUnit (balabanG (-(adOp Y))) := by
  have hnorm : ‖adOp Y‖ < Real.log 2 := by
    have := norm_adOp_le Y
    linarith
  have hneg : ‖-(adOp Y)‖ < Real.log 2 := by rwa [norm_neg]
  exact ⟨isUnit_balabanG_of_norm_lt_log_two hnorm,
    isUnit_balabanG_of_norm_lt_log_two hneg⟩

end Nontrivial

end Complete

end YangMills.CMP98Eq119
