/-
# Row A1a — the constrained first variation with all indices visible

The Gaussian floor needs the *constrained* first background variation
`V = D_background Δ̂` of the fluctuation operator, not merely the background
derivative of the Wilson Hessian.  The constrained quadratic form is built from

* the background Wilson Hessian `Δ(U) = D_U^*D_U + Δ'(U)`,
* the background-dependent linear part `Q_j(U)` of the averaging operation, and
* the gauge/constrained projection,

so its background derivative has three pieces,

    V_constrained = W + Q + R,
      W = D_bg Δ(U),   Q = D_bg Q_j(U),   R = D_bg (gauge/constrained projection).

This file fixes that decomposition with **every index visible** — two
fluctuation Lorentz indices, one background Lorentz index, three colour indices
and the momentum — so that a collapsed scalar `V_{00}` cannot silently be an
identically vanishing all-equal component (`WilsonCubicVertex.wilsonCubic_allEqual`).

What is proved:

* `wilsonPiece_allEqual_zero` : if the `W` piece is the literal Wilson cubic
  vertex then its all-equal Lorentz component vanishes identically — the
  concrete reason the background index must be kept.
* `component_ne_zero_imp` : a nonzero component of `V` forces one of `W, Q, R`
  to be nonzero there; nothing can be read off `V` without them.
* `wilsonPiece_positive_but_total_zero` : an explicit constrained variation
  whose `W` piece is strictly positive at a momentum while `W + Q + R` vanishes
  there.  So a positive patch certified from `W` alone is **not** a certificate
  for `V`: the `Q` and `R` variations may not be assumed to vanish.
* `patchBound_of_wilson_and_remainder` : the correct compiler — a lower bound
  `c` on `W` over a patch together with a bound `e` on `|Q| + |R|` over the same
  patch gives the lower bound `c − e` for `V`, which is what
  `PositivePatchEnclosure` consumes.

Nothing here asserts the literal values of `W`, `Q` or `R`.
-/
import RequestProject.YangMills.WilsonCubicVertex

namespace YangMills

/-- A fully index-resolved momentum-space symbol of a cubic vertex: two
fluctuation Lorentz indices `α β`, one background Lorentz index `ρ`, three
colour indices `a b c`, and the momentum. -/
abbrev VertexSymbol (color : Type*) : Type _ :=
  Fin 4 → Fin 4 → Fin 4 → color → color → color → (Fin 4 → ℝ) → ℝ

/-- The three source-native pieces of the constrained first background
variation. -/
structure ConstrainedFirstVariation (color : Type*) where
  /-- background derivative of the Wilson Hessian `Δ(U)` -/
  W : VertexSymbol color
  /-- background derivative of the averaging operator `Q_j(U)` -/
  Q : VertexSymbol color
  /-- background derivative of the gauge/constrained projection -/
  R : VertexSymbol color

namespace ConstrainedFirstVariation

variable {color : Type*}

/-- The constrained first variation itself: `V = W + Q + R`. -/
def total (V : ConstrainedFirstVariation color) : VertexSymbol color :=
  fun al be rho a b c q => V.W al be rho a b c q + V.Q al be rho a b c q
    + V.R al be rho a b c q

theorem total_apply (V : ConstrainedFirstVariation color)
    (al be rho : Fin 4) (a b c : color) (q : Fin 4 → ℝ) :
    V.total al be rho a b c q
      = V.W al be rho a b c q + V.Q al be rho a b c q + V.R al be rho a b c q := rfl

/-- A nonzero component of the constrained variation forces one of the three
pieces to be nonzero there. -/
theorem component_ne_zero_imp (V : ConstrainedFirstVariation color)
    {al be rho : Fin 4} {a b c : color} {q : Fin 4 → ℝ}
    (h : V.total al be rho a b c q ≠ 0) :
    V.W al be rho a b c q ≠ 0 ∨ V.Q al be rho a b c q ≠ 0
      ∨ V.R al be rho a b c q ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨hW, hQ, hR⟩ := hcon
  exact h (by rw [total_apply, hW, hQ, hR]; ring)

/-- **The correct patch compiler.**  A lower bound `c` for the Wilson piece over
a set of momenta, together with a bound `e` on the size of the averaging and
projection variations there, gives the lower bound `c − e` for the constrained
variation on that set. -/
theorem patchBound_of_wilson_and_remainder (V : ConstrainedFirstVariation color)
    {P : Set (Fin 4 → ℝ)} {al be rho : Fin 4} {a b c : color} {cval e : ℝ}
    (hW : ∀ q ∈ P, cval ≤ V.W al be rho a b c q)
    (hQR : ∀ q ∈ P, |V.Q al be rho a b c q| + |V.R al be rho a b c q| ≤ e) :
    ∀ q ∈ P, cval - e ≤ V.total al be rho a b c q := by
  intro q hq
  have h1 := hW q hq
  have h2 := hQR q hq
  have hQ : -|V.Q al be rho a b c q| ≤ V.Q al be rho a b c q := neg_abs_le _
  have hR : -|V.R al be rho a b c q| ≤ V.R al be rho a b c q := neg_abs_le _
  rw [total_apply]
  linarith

end ConstrainedFirstVariation

/-- The Wilson piece built from the literal Wilson cubic vertex (colour indices
carried by a structure constant factor `f`). -/
noncomputable def wilsonPiece {color : Type*} (f : color → color → color → ℝ) :
    VertexSymbol color :=
  fun al be rho a b c q => f a b c * wilsonCubic q (fun mu => -q mu) (fun _ => 0) al be rho

/-- **The all-equal Lorentz component of the Wilson piece vanishes
identically.**  A scalar written `V_{00}` must therefore not be the all-equal
component: the background Lorentz index has to remain visible. -/
theorem wilsonPiece_allEqual_zero {color : Type*} (f : color → color → color → ℝ)
    (mu : Fin 4) (a b c : color) (q : Fin 4 → ℝ) :
    wilsonPiece f mu mu mu a b c q = 0 := by
  simp [wilsonPiece, wilsonCubic_allEqual]

/-- The Wilson piece also vanishes on the whole diagonal at any corner momentum
(`WilsonCubicVertex.wilsonCubic_bgZero_diag_corner_eq_zero`), for every
background index. -/
theorem wilsonPiece_diag_corner_zero {color : Type*} (f : color → color → color → ℝ)
    {q : Fin 4 → ℝ} (hq : IsCornerMomentum q) (mu rho : Fin 4) (a b c : color) :
    wilsonPiece f mu mu rho a b c q = 0 := by
  have := wilsonCubic_bgZero_diag_corner_eq_zero hq mu rho
  simp [wilsonPiece, wilsonCubicBgZero] at this ⊢
  simp [this]

/-- **`Q` and `R` may not be assumed to vanish.**  There is a constrained first
variation whose Wilson piece is strictly positive at a momentum while the
constrained variation `W + Q + R` vanishes there.  Hence a positive patch
certified from the Wilson piece alone is not a certificate for the constrained
variation. -/
theorem wilsonPiece_positive_but_total_zero :
    ∃ V : ConstrainedFirstVariation Unit,
      (∀ q : Fin 4 → ℝ, 0 < V.W 0 0 1 () () () q) ∧
      (∀ q : Fin 4 → ℝ, V.total 0 0 1 () () () q = 0) := by
  refine ⟨{ W := fun _ _ _ _ _ _ _ => 1
          , Q := fun _ _ _ _ _ _ _ => -1
          , R := fun _ _ _ _ _ _ _ => 0 }, fun q => by norm_num, fun q => by
      simp [ConstrainedFirstVariation.total]⟩

end YangMills
