/-
# Row A — the trajectory produced by the shell bound satisfies the
coupling-window hypothesis of the published small-field RG theorem

## The source statement being targeted

The theorem of the Bałaban RG paper (CMP 109) that this file feeds is, in the
formulation supplied with the task:

> for an arbitrary semisimple compact `G ⊂ U(N)` in `d = 4`, if the entire
> effective-coupling sequence remains in a sufficiently small interval, then the
> small-field effective actions have the required form, with uniform analytic
> bounds.

So the theorem is an implication whose hypothesis is a *coupling window* — a
uniform statement `0 < g_j ≤ γ` over all effective scales — and whose conclusion
is the small-field effective-action/analyticity package.  This file supplies the
hypothesis from the Row A shell bound, and consumes the implication.

## What is proved

* `CouplingWindow` — the hypothesis: `0 < g_j ≤ γ` at every effective scale.
* `couplingSq_two_sided_rate` — the quantitative two-sided content of the Row A
  trajectory: with `b₋ ≤ β_j ≤ b₊`,
  `(u₀ + b₊ j)⁻¹ ≤ g_j² ≤ (u₀ + b₋ j)⁻¹`.
* `couplingWindow_of_positiveShell` — a uniformly positive shell coefficient and
  a bare coupling inside the window put the *whole* sequence inside the window:
  `0 < g_j ≤ γ` for all `j`.  Monotone descent, no extra assumption.
* `effectiveCoupling_pos_lower` — the two-sided version: the window is entered
  and never left, and at each finite scale the coupling is also bounded below by
  `√((u₀ + b₊ j)⁻¹) > 0`, so the window is not entered by collapsing to zero at
  a finite scale.
* `cmp109Thm1_package_of_window` — consumption of the source implication: given
  the published theorem in the explicit form
  `∀ g, CouplingWindow γ g → Pkg g`, the Row A trajectory satisfies `Pkg`.
* `cmp109Thm1_package_of_shellKernels` — the end-to-end Row A form: from the
  literal kernel data of the averaging/constrained-projection variation and of
  the seagull, the shell coefficient is `≥ 1/16777216`, hence the trajectory is
  in the window, hence the published package applies to it.

## Honest status — what is a socket and what is a theorem

`cmp109Thm1_package_of_window` and `cmp109Thm1_package_of_shellKernels` take the
published theorem as an explicit hypothesis `thm1`.  That hypothesis is an
**open socket**: it is the statement of the source theorem, not a proof of it,
and nothing in this development proves it.  What *is* proved here is that the
Row A trajectory inhabits its hypothesis — i.e. the coupling window — with no
correspondence assumption left on that side.

The group-theoretic side is worth recording explicitly: no structure constant,
Casimir or Ward scalar of a particular group enters any statement in this file.
The window argument is uniform in the gauge group, which is the same generality
as the source theorem for arbitrary semisimple compact `G ⊂ U(N)`.  The
SU(2)-specific quantitative theorem of the source is therefore *not* needed to
supply this hypothesis; see the accompanying report for the line-by-line
comparison.
-/
import RequestProject.YangMills.RowATrajectory

namespace YangMills

open Filter Topology Real

/-! ## 1. The window -/

/-- **The coupling-window hypothesis**: the whole effective-coupling sequence
lies in `(0, γ]`. -/
structure CouplingWindow (gamma : ℝ) (g : ℕ → ℝ) : Prop where
  pos : ∀ j, 0 < g j
  le : ∀ j, g j ≤ gamma

/-- The effective coupling of the trajectory: `g_j = √(u_j⁻¹)`. -/
noncomputable def effectiveCoupling (u : ℕ → ℝ) (j : ℕ) : ℝ := Real.sqrt (couplingSq u j)

/-! ## 2. The two-sided rate -/

variable {u beta : ℕ → ℝ} {bm bp : ℝ}

/-- **The two-sided rate of the Row A trajectory.**  A shell coefficient trapped
between `b₋` and `b₊` traps the squared coupling between `(u₀ + b₊ j)⁻¹` and
`(u₀ + b₋ j)⁻¹`. -/
theorem couplingSq_two_sided_rate (hstep : ∀ j, u (j + 1) = u j + beta j)
    (hbl : ∀ j, bm ≤ beta j) (hbu : ∀ j, beta j ≤ bp) (hbm : 0 ≤ bm) (hu0 : 0 < u 0)
    (j : ℕ) :
    (u 0 + bp * j)⁻¹ ≤ couplingSq u j ∧ couplingSq u j ≤ (u 0 + bm * j)⁻¹ :=
  ⟨(coupling_pos hstep hbl hbu hbm hu0 j).2, couplingSq_le hstep hbl hbm hu0 j⟩

/-! ## 3. The window is entered and never left -/

/-- **The Row A trajectory satisfies the coupling-window hypothesis.**  A
uniformly positive shell coefficient makes the inverse coupling increase, so the
squared coupling never exceeds its initial value; if the bare coupling is inside
the window, the whole sequence is. -/
theorem couplingWindow_of_positiveShell {gamma : ℝ}
    (hstep : ∀ j, u (j + 1) = u j + beta j)
    (hbl : ∀ j, bm ≤ beta j) (hbm : 0 ≤ bm) (hu0 : 0 < u 0)
    (hgamma : 0 ≤ gamma) (hstart : (u 0)⁻¹ ≤ gamma ^ 2) :
    CouplingWindow gamma (effectiveCoupling u) := by
  refine ⟨fun j => ?_, fun j => ?_⟩
  · have hupos := inverseCoupling_pos hstep hbl hbm hu0 j
    exact Real.sqrt_pos.mpr (inv_pos.mpr hupos)
  · have hle := couplingSq_le hstep hbl hbm hu0 j
    have hjnn : (0 : ℝ) ≤ bm * j := by positivity
    have hden : 0 < u 0 + bm * j := by linarith
    have hmono : (u 0 + bm * j)⁻¹ ≤ (u 0)⁻¹ := by
      exact inv_anti₀ hu0 (by linarith)
    have hchain : couplingSq u j ≤ gamma ^ 2 := le_trans hle (le_trans hmono hstart)
    calc effectiveCoupling u j = Real.sqrt (couplingSq u j) := rfl
      _ ≤ Real.sqrt (gamma ^ 2) := Real.sqrt_le_sqrt hchain
      _ = gamma := by rw [Real.sqrt_sq hgamma]

/-- **The window is nondegenerate at every finite scale.**  With a two-sided
shell coefficient the effective coupling is also bounded below by
`√((u₀ + b₊ j)⁻¹) > 0`: the trajectory approaches the origin of the window only
in the limit, never at a finite scale. -/
theorem effectiveCoupling_pos_lower (hstep : ∀ j, u (j + 1) = u j + beta j)
    (hbl : ∀ j, bm ≤ beta j) (hbu : ∀ j, beta j ≤ bp) (hbm : 0 ≤ bm) (hu0 : 0 < u 0)
    (j : ℕ) :
    Real.sqrt ((u 0 + bp * j)⁻¹) ≤ effectiveCoupling u j :=
  Real.sqrt_le_sqrt (coupling_pos hstep hbl hbu hbm hu0 j).2

/-! ## 4. Consuming the published theorem -/

/-- **The published small-field theorem applied to the Row A trajectory.**

`thm1` is the source implication in its literal shape — coupling window in,
small-field effective-action/analyticity package out — supplied as an explicit
hypothesis (an open socket, not proved here).  Everything else is the Row A
trajectory result: the shell bound puts the whole effective-coupling sequence
inside the window. -/
theorem cmp109Thm1_package_of_window {gamma : ℝ} {Pkg : (ℕ → ℝ) → Prop}
    (thm1 : ∀ g : ℕ → ℝ, CouplingWindow gamma g → Pkg g)
    (hstep : ∀ j, u (j + 1) = u j + beta j)
    (hbl : ∀ j, bm ≤ beta j) (hbm : 0 ≤ bm) (hu0 : 0 < u 0)
    (hgamma : 0 ≤ gamma) (hstart : (u 0)⁻¹ ≤ gamma ^ 2) :
    Pkg (effectiveCoupling u) :=
  thm1 _ (couplingWindow_of_positiveShell hstep hbl hbm hu0 hgamma hstart)

/-- **Row A end to end, up to the published theorem.**  From the literal kernel
data of the Gaussian sector and the channel bounds of the interaction sector,
the shell coefficient is at least `1/16777216`; the induced trajectory therefore
lies in the coupling window at every effective scale, and the published
small-field package applies to it.

The only unproved input is `thm1`, the source theorem itself. -/
theorem cmp109Thm1_package_of_shellKernels
    {ι κ ξ ζ : Type*} [Fintype ι] [Fintype κ] [Fintype ξ] [Fintype ζ]
    {Adm : (ℕ → ℝ) → Prop} {g : ℕ → ℝ} {f R M MW : ℝ}
    {Kk : ℕ → (ℕ → ℝ) → Fin 4 → ξ → ℝ} {dd : ℕ → (ℕ → ℝ) → Fin 4 → ξ → (Fin 4 → ℝ)}
    {KW : ℕ → (ℕ → ℝ) → Fin 4 → Fin 4 → ζ → ℝ}
    {dW : ℕ → (ℕ → ℝ) → Fin 4 → Fin 4 → ζ → (Fin 4 → ℝ)}
    {lamDet : ℕ → (ℕ → ℝ) → ι → ℝ} {lamGauge : ℕ → (ℕ → ℝ) → κ → ℝ}
    {aInt aChart aLoc : ℕ → (ℕ → ℝ) → ℕ → ℝ}
    {AInt AChart ALoc : ℕ → ℝ} {N : ℕ} {LamDet LamGauge theta : ℝ}
    {gamma : ℝ} {Pkg : (ℕ → ℝ) → Prop}
    (thm1 : ∀ gg : ℕ → ℝ, CouplingWindow gamma gg → Pkg gg)
    (hR : 0 ≤ R) (hM : 0 ≤ M) (hMW : 0 ≤ MW)
    (hzero : ∀ j h a, ∑ i, Kk j h a i = 0)
    (hd : ∀ j h a i mu, |dd j h a i mu| ≤ R)
    (hmass : ∀ j h a, kernelMass (Kk j h a) ≤ M)
    (hsmallK : linearVanishingConstant R M ≤ 1 / 2)
    (hmassW : ∀ j h a b, kernelMass (KW j h a b) ≤ MW)
    (hLd : ∀ j h i, |lamDet j h i| ≤ LamDet)
    (hLg : ∀ j h i, |lamGauge j h i| ≤ LamGauge)
    (hAInt : ∀ j h n, |aInt j h n| ≤ AInt n)
    (hAChart : ∀ j h n, |aChart j h n| ≤ AChart n)
    (hALoc : ∀ j h n, |aLoc j h n| ≤ ALoc n)
    (hsmall : ∀ j h, Adm h → 0 ≤ h j ∧ h j ≤ theta ∧
        h j * LamDet ≤ theta ∧ h j * LamGauge ≤ theta)
    (hth : theta < 1) (hth0 : 0 ≤ theta)
    (hadm : Adm g) (hg0 : ∀ j, 0 ≤ g j)
    (hgg : ∀ j, g j ≤ criticalCoupling (1 / 8388608 : ℝ)
      (Cbeta (sourceChannelCoefficient (Fintype.card ι) (Fintype.card κ)
        LamDet LamGauge theta AInt AChart ALoc N)))
    (hu0 : 0 < u 0)
    (hstep : ∀ j, u (j + 1) = u j + shellBetaOfSources
      (fun j' h => literalOneLoopIntegrand
        (sourceVariationMatrix f 1 (diagCosSymbolMatrix (Kk j' h) (dd j' h)))
        (cosSymbolMatrix (KW j' h) (dW j' h)))
      lamDet lamGauge aInt aChart aLoc N j g)
    (hgamma : 0 ≤ gamma) (hstart : (u 0)⁻¹ ≤ gamma ^ 2) :
    Pkg (effectiveCoupling u) := by
  have hbl : ∀ j, (1 : ℝ) / 16777216 ≤ shellBetaOfSources
      (fun j' h => literalOneLoopIntegrand
        (sourceVariationMatrix f 1 (diagCosSymbolMatrix (Kk j' h) (dd j' h)))
        (cosSymbolMatrix (KW j' h) (dW j' h)))
      lamDet lamGauge aInt aChart aLoc N j g := fun j =>
    A1_beta_pos_ward_from_kernels hR hM hMW hzero hd hmass hsmallK hmassW hLd hLg
      hAInt hAChart hALoc hsmall hth hth0 hadm hg0 hgg j
  exact cmp109Thm1_package_of_window thm1 hstep hbl (by norm_num) hu0 hgamma hstart

end YangMills
