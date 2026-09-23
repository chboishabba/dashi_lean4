/-
# Row A1a — the operator variation `A'` as the mixed **third** Wilson variation

`ConstraintCoordinateGaussian` splits the first variation of the restricted
Gaussian as `V = W + Q + R` with `W = Cᵀ A' C`.  Here `A(s)` is the Wilson
Hessian in the fluctuation directions, evaluated on the background family, so
its background derivative `A'` is the **mixed third** variation of the Wilson
action — not the first, and not the Hessian itself:

    D S  →  D² S = A  →  D³ S = A'.

`MixedThirdVariation`/`WilsonLinkJet` produce `D³S` for exponential link
families.  This file supplies the missing glue: it assembles the per-entry
third-variation data into a *matrix* family whose derivative is `A'`, and feeds
that into the restricted-Gaussian and patch machinery.

* `WilsonHessianData` : per-entry nested derivative data
  (`∂_u`, then `∂_t`, then `∂_s`) for a matrix of scalar three-parameter
  actions.  No derivative is postulated: each is a `HasDerivAt` hypothesis, and
  `WilsonHessianData.hasMixedD3R_entry` shows the data really exhibits the
  entrywise mixed third derivative.
* `WilsonHessianData.hessian` / `hasMatDerivAt_hessian` : the Hessian family
  `A(s)` and the identification `A' = D³S`.
* `wilsonThird_restricted_variation` : the resulting restricted first variation
  `D Â = Cᵀ(D³S)C + Q + R`, i.e. the Wilson component of the Gaussian symbol is
  literally the third variation conjugated by the substitution.
* `wilsonThird_patch_entry_bound` : the compiler — a floor `c` for the diagonal
  entry of `Cᵀ(D³S)C` on a patch and the connection budget `e` give the floor
  `c − 2e` for the full restricted symbol there.
* `hessian_zero_but_third_nonzero` : the honest boundary test.  There are data
  with vanishing Hessian at the background point and nonvanishing third
  variation, so `W` cannot be read off from `D²S`; the third-order calculation is
  genuinely required.

**Honest status.**  No numerical value of `D³S` for Bałaban's background is
supplied here, so the Wilson floor `c` is still open and Row A1 does not close.
What is closed is the ancestry `D³S ⇒ A' ⇒ W` and its interface to the patch
test.
-/
import RequestProject.YangMills.WilsonLinkJet
import RequestProject.YangMills.ConnectionBudget

namespace YangMills

open Matrix

variable {m : Type*}

/-- Per-entry nested derivative data for a matrix of scalar three-parameter
Wilson actions: `u`-derivative `g`, then `t`-derivative `hess` (the Hessian
entry as a function of the background), then `s`-derivative `third`. -/
structure WilsonHessianData (m : Type*) where
  /-- the entrywise action `S_{ab}(s, t, u)`: background `s`, fluctuations `t, u` -/
  S : m → m → ℝ → ℝ → ℝ → ℝ
  /-- the `u`-derivative at `u = 0` -/
  g : m → m → ℝ → ℝ → ℝ
  /-- the Hessian entry, as a function of the background parameter -/
  hess : m → m → ℝ → ℝ
  /-- the mixed third variation -/
  third : Matrix m m ℝ
  hu : ∀ a b s t, HasDerivAt (fun u => S a b s t u) (g a b s t) 0
  ht : ∀ a b s, HasDerivAt (fun t => g a b s t) (hess a b s) 0
  hs : ∀ a b, HasDerivAt (hess a b) (third a b) 0

namespace WilsonHessianData

variable (D : WilsonHessianData m)

/-- The Wilson Hessian family `A(s)` in the fluctuation directions. -/
def hessian (s : ℝ) : Matrix m m ℝ := Matrix.of fun a b => D.hess a b s

/-- **The data really exhibits the entrywise mixed third derivative.** -/
theorem hasMixedD3R_entry (a b : m) : HasMixedD3R (D.S a b) (D.third a b) :=
  ⟨D.g a b, fun s t => D.hu a b s t, D.hess a b, fun s => D.ht a b s, D.hs a b⟩

/-- **`A' = D³S`.**  The background derivative of the Wilson Hessian family is
the mixed third variation. -/
theorem hasMatDerivAt_hessian : HasMatDerivAt D.hessian D.third 0 :=
  fun a b => D.hs a b

end WilsonHessianData

/-- **The restricted first variation with the Wilson component instantiated.**
For a differentiable substitution family `C(s)`, the first variation of the
restricted Gaussian `Â = CᵀAC` is `Cᵀ(D³S)C + Q + R`. -/
theorem wilsonThird_restricted_variation {n : Type*} [Fintype n]
    (D : WilsonHessianData n) {C : ℝ → Matrix n m ℝ} {C' : Matrix n m ℝ}
    (hC : HasMatDerivAt C C' 0) :
    HasMatDerivAt (fun s => restricted (C s) (D.hessian s))
      (opVariation (C 0) D.third + connectionLeft (C 0) C' (D.hessian 0)
        + connectionRight (C 0) C' (D.hessian 0)) 0 :=
  restrictedVariation_eq_W_add_Q_add_R hC D.hasMatDerivAt_hessian

/-- **The patch compiler from the third variation.**  A floor `c` for the
diagonal entry of the conjugated third variation `Cᵀ(D³S)C`, together with the
connection budget `e`, gives the floor `c − 2e` for the full restricted first
variation entry. -/
theorem wilsonThird_patch_entry_bound {n : Type*} [Fintype n]
    (D : WilsonHessianData n) (C C' : Matrix n m ℝ)
    (hA : (D.hessian 0)ᵀ = D.hessian 0) (i : m) {c e : ℝ}
    (hW : c ≤ opVariation C D.third i i)
    (hR : |connectionRight C C' (D.hessian 0) i i| ≤ e) :
    c - 2 * e ≤ (opVariation C D.third + connectionLeft C C' (D.hessian 0)
      + connectionRight C C' (D.hessian 0)) i i :=
  restrictedVariation_entry_lower_bound C C' hA D.third i hW hR

/-- **The Hessian does not see the Wilson component.**  There is admissible data
whose Hessian vanishes identically at the background point while the mixed third
variation is nonzero — so `W` must be computed at third order. -/
theorem hessian_zero_but_third_nonzero :
    ∃ D : WilsonHessianData (Fin 1), D.hessian 0 = 0 ∧ D.third ≠ 0 := by
  refine ⟨{ S := fun _ _ s t u => s * t * u
            g := fun _ _ s t => s * t
            hess := fun _ _ s => s
            third := Matrix.of fun _ _ => 1
            hu := fun _ _ s t => by
              simpa using (hasDerivAt_id (0 : ℝ)).const_mul (s * t)
            ht := fun _ _ s => by
              simpa using (hasDerivAt_id (0 : ℝ)).const_mul s
            hs := fun _ _ => by simpa using hasDerivAt_id (0 : ℝ) }, ?_, ?_⟩
  · funext a b
    simp [WilsonHessianData.hessian]
  · intro h
    have := congrFun (congrFun h 0) 0
    simp at this

end YangMills
