/-
# Uniqueness on a finite time window

`Uniqueness.lean` proves uniqueness for solutions defined for all times.  The
Cauchy theory needs the same statement on a finite window `[0,T)`, where the
momentum equation and incompressibility are only available inside the window.
Every ingredient of the energy argument is now available in a form that uses the
equations at a single time (`global_quadratic_balance_at`,
`cellInt_pressure_work_eq_zero_at`, `momentum_component_at`), and the Grönwall
step is run as an `AntitoneOn` statement on `[0,t]`.

Moreover the gradient bound that the energy argument needs is *free* on the
torus: `exists_gradient_bound_on_slab` produces it from compactness.  So the
window uniqueness statement carries no extra hypothesis at all, and
`ClayNS.WindowUniquenessGate` is discharged here
(`ClayNS.windowUniquenessGate_holds`).

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.OpenGates
import RequestProject.NavierStokes.PeriodicBounded
import RequestProject.NavierStokes.Uniqueness

open scoped BigOperators
open MeasureTheory Set

noncomputable section

namespace ClayNS

/-- **Uniqueness in the energy norm on a window.**  The cell energy of the
difference of two window solutions with the same datum vanishes throughout the
window. -/
theorem difference_energy_zero_on (nu M T : ℝ) (V V' : STime → E3) (P P' : STime → ℝ)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hV' : ContDiff ℝ (⊤ : ℕ∞) V')
    (hP : ContDiff ℝ (⊤ : ℕ∞) P) (hP' : ContDiff ℝ (⊤ : ℕ∞) P')
    (hVper : SpacePeriodic V) (hV'per : SpacePeriodic V')
    (hPper : SpacePeriodic P) (hP'per : SpacePeriodic P')
    (hnu : 0 ≤ nu)
    (hdiv : ∀ z : STime, 0 ≤ z.1 → z.1 < T → divg V z = 0)
    (hdiv' : ∀ z : STime, 0 ≤ z.1 → z.1 < T → divg V' z = 0)
    (hmom : ∀ z : STime, 0 ≤ z.1 → z.1 < T →
      dtime V z + adv V z = - grad P z + nu • lap V z)
    (hmom' : ∀ z : STime, 0 ≤ z.1 → z.1 < T →
      dtime V' z + adv V' z = - grad P' z + nu • lap V' z)
    (hM : ∀ z : STime, 0 ≤ z.1 → z.1 < T → ∀ j a : Fin 3,
      |dvec (0, ee j) (fun w => V' w a) z| ≤ M)
    (hinit : ∀ x : E3, V (0, x) = V' (0, x))
    {t : ℝ} (ht : 0 ≤ t) (htT : t < T) :
    cellInt (fun x => quad (fun a w => V w a - V' w a) (t, x)) = 0 := by
  classical
  have hVc : ∀ i : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun w => V w i) := fun i => contDiff_coord V hV i
  have hV'c : ∀ i : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun w => V' w i) :=
    fun i => contDiff_coord V' hV' i
  have hcoordsub : ∀ (w : STime) (a : Fin 3), (V w - V' w) a = V w a - V' w a := by
    intro w a; simp
  -- the difference fields
  have hWsmooth : ∀ a : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun w => V w a - V' w a) :=
    fun a => (hVc a).sub (hV'c a)
  have hWper : ∀ a : Fin 3, SpacePeriodic (fun w => V w a - V' w a) := by
    intro a z j
    have h1 : V (z.1, z.2 + ee j) a = V z a := spacePeriodic_coord hVper a z j
    have h2 : V' (z.1, z.2 + ee j) a = V' z a := spacePeriodic_coord hV'per a z j
    show V (z.1, z.2 + ee j) a - V' (z.1, z.2 + ee j) a = V z a - V' z a
    rw [h1, h2]
  have hWv : ContDiff ℝ (⊤ : ℕ∞) (fun w => V w - V' w) := hV.sub hV'
  have hWvper : SpacePeriodic (fun w => V w - V' w) := by
    intro z j
    show V (z.1, z.2 + ee j) - V' (z.1, z.2 + ee j) = V z - V' z
    rw [hVper z j, hV'per z j]
  have hQ : ContDiff ℝ (⊤ : ℕ∞) (fun w => P w - P' w) := hP.sub hP'
  have hQper : SpacePeriodic (fun w => P w - P' w) := by
    intro z j
    show P (z.1, z.2 + ee j) - P' (z.1, z.2 + ee j) = P z - P' z
    rw [hPper z j, hP'per z j]
  have hWvdiv : ∀ s : ℝ, 0 ≤ s → s < T → ∀ x : E3,
      divg (fun y => V y - V' y) (s, x) = 0 := by
    intro s hs hsT x
    rw [divg_sub V V' hV hV' (s, x), hdiv (s, x) hs hsT, hdiv' (s, x) hs hsT, sub_zero]
  -- the balance for the difference, at every time of the window
  have hbal : ∀ s : ℝ, 0 ≤ s → s < T →
      HasDerivAt (fun r => cellInt (fun x => quad (fun a w => V w a - V' w a) (r, x)))
        (cellInt (fun x => ∑ a, (V (s, x) a - V' (s, x) a)
            * (-(∑ j, (V (s, x) j - V' (s, x) j) * dvec (0, ee j) (fun y => V' y a) (s, x))
                - dvec (0, ee a) (fun y => P y - P' y) (s, x)))
          - nu * cellInt (fun x => gradSq (fun a w => V w a - V' w a) (s, x))) s := by
    intro s hs hsT
    exact global_quadratic_balance_at nu V (fun a w => V w a - V' w a)
      (fun a w => -(∑ j, (V w j - V' w j) * dvec (0, ee j) (fun y => V' y a) w)
        - dvec (0, ee a) (fun y => P y - P' y) w)
      hV hVper hWsmooth hWper s (fun x => hdiv (s, x) hs hsT)
      (fun a x => difference_transport nu V V' P P' hV hV' hP hP' a (s, x)
        (hmom (s, x) hs hsT) (hmom' (s, x) hs hsT))
  set K : ℝ → ℝ := fun s => cellInt (fun x => quad (fun a w => V w a - V' w a) (s, x)) with hK
  -- continuity of the integrands
  have hcStretch : ∀ s : ℝ, Continuous (fun x : E3 =>
      ∑ a, (V (s, x) a - V' (s, x) a)
        * ∑ j, (V (s, x) j - V' (s, x) j) * (-(dvec (0, ee j) (fun y => V' y a) (s, x)))) := by
    intro s
    refine continuous_time_slice (f := fun w : STime => ∑ a, (V w a - V' w a)
      * ∑ j, (V w j - V' w j) * (-(dvec (0, ee j) (fun y => V' y a) w))) ?_ s
    refine continuous_finset_sum _ fun a _ => (hWsmooth a).continuous.mul ?_
    exact continuous_finset_sum _ fun j _ =>
      (hWsmooth j).continuous.mul (continuous_dvec _ (hV'c a) (0, ee j)).neg
  have hcPress : ∀ s : ℝ, Continuous (fun x : E3 =>
      ∑ a, (V (s, x) a - V' (s, x) a) * dvec (0, ee a) (fun y => P y - P' y) (s, x)) := by
    intro s
    refine continuous_time_slice (f := fun w : STime => ∑ a, (V w a - V' w a)
      * dvec (0, ee a) (fun y => P y - P' y) w) ?_ s
    exact continuous_finset_sum _ fun a _ =>
      (hWsmooth a).continuous.mul (continuous_dvec _ hQ (0, ee a))
  have hcQuad : ∀ s : ℝ, Continuous (fun x : E3 =>
      6 * M * quad (fun a w => V w a - V' w a) (s, x)) :=
    fun s => continuous_const.mul (continuous_time_slice (contDiff_quad _ hWsmooth).continuous s)
  -- the source integral is at most `6 M K`
  have hsrc : ∀ s : ℝ, 0 ≤ s → s < T → cellInt (fun x => ∑ a, (V (s, x) a - V' (s, x) a)
        * (-(∑ j, (V (s, x) j - V' (s, x) j) * dvec (0, ee j) (fun y => V' y a) (s, x))
            - dvec (0, ee a) (fun y => P y - P' y) (s, x)))
      ≤ 6 * M * K s := by
    intro s hs hsT
    have hsplit : ∀ x : E3, (∑ a, (V (s, x) a - V' (s, x) a)
        * (-(∑ j, (V (s, x) j - V' (s, x) j) * dvec (0, ee j) (fun y => V' y a) (s, x))
            - dvec (0, ee a) (fun y => P y - P' y) (s, x)))
      = (∑ a, (V (s, x) a - V' (s, x) a)
            * ∑ j, (V (s, x) j - V' (s, x) j) * (-(dvec (0, ee j) (fun y => V' y a) (s, x))))
          - ∑ a, (V (s, x) a - V' (s, x) a)
              * dvec (0, ee a) (fun y => P y - P' y) (s, x) := by
      intro x
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      have hneg : ∑ j, (V (s, x) j - V' (s, x) j) * (-(dvec (0, ee j) (fun y => V' y a) (s, x)))
          = -(∑ j, (V (s, x) j - V' (s, x) j) * dvec (0, ee j) (fun y => V' y a) (s, x)) := by
        simp [mul_neg]
      rw [hneg]
      ring
    have e1 : cellInt (fun x : E3 => ∑ a, (V (s, x) a - V' (s, x) a)
          * (-(∑ j, (V (s, x) j - V' (s, x) j) * dvec (0, ee j) (fun y => V' y a) (s, x))
              - dvec (0, ee a) (fun y => P y - P' y) (s, x)))
        = cellInt (fun x : E3 => ∑ a, (V (s, x) a - V' (s, x) a)
            * ∑ j, (V (s, x) j - V' (s, x) j) * (-(dvec (0, ee j) (fun y => V' y a) (s, x))))
          - cellInt (fun x : E3 => ∑ a, (V (s, x) a - V' (s, x) a)
              * dvec (0, ee a) (fun y => P y - P' y) (s, x)) := by
      rw [cellInt_congr hsplit]
      exact cellInt_sub (hcStretch s) (hcPress s)
    -- the pressure work integrates away
    have e2 : cellInt (fun x : E3 => ∑ a, (V (s, x) a - V' (s, x) a)
        * dvec (0, ee a) (fun y => P y - P' y) (s, x)) = 0 := by
      have h0 := cellInt_pressure_work_eq_zero_at (fun w => V w - V' w) (fun w => P w - P' w)
        hWv hQ hWvper hQper s (hWvdiv s hs hsT)
      have hcg : cellInt (fun x : E3 => ∑ a, ((V (s, x) - V' (s, x)) a)
            * dvec (0, ee a) (fun y => P y - P' y) (s, x))
          = cellInt (fun x : E3 => ∑ a, (V (s, x) a - V' (s, x) a)
            * dvec (0, ee a) (fun y => P y - P' y) (s, x)) :=
        cellInt_congr fun x => Finset.sum_congr rfl fun a _ => by rw [hcoordsub]
      rw [← hcg]
      exact h0
    -- the stretching term is controlled by the gradient bound
    have e3 : cellInt (fun x : E3 => ∑ a, (V (s, x) a - V' (s, x) a)
          * ∑ j, (V (s, x) j - V' (s, x) j) * (-(dvec (0, ee j) (fun y => V' y a) (s, x))))
        ≤ 6 * M * K s := by
      have hA : ∀ x : E3, (∑ a, (V (s, x) a - V' (s, x) a)
            * ∑ j, (V (s, x) j - V' (s, x) j) * (-(dvec (0, ee j) (fun y => V' y a) (s, x))))
          ≤ 6 * M * quad (fun a w => V w a - V' w a) (s, x) := by
        intro x
        have h := stretching_bound M (fun a => V (s, x) a - V' (s, x) a)
          (fun j a => -(dvec (0, ee j) (fun y => V' y a) (s, x)))
          (fun j a => by rw [abs_neg]; exact hM (s, x) hs hsT j a)
        have hq : quad (fun a w => V w a - V' w a) (s, x)
            = (1 / 2 : ℝ) * ∑ a, (V (s, x) a - V' (s, x) a) * (V (s, x) a - V' (s, x) a) := rfl
        rw [hq]
        linarith
      calc cellInt (fun x : E3 => ∑ a, (V (s, x) a - V' (s, x) a)
              * ∑ j, (V (s, x) j - V' (s, x) j) * (-(dvec (0, ee j) (fun y => V' y a) (s, x))))
          ≤ cellInt (fun x : E3 => 6 * M * quad (fun a w => V w a - V' w a) (s, x)) :=
            cellInt_mono (hcStretch s) (hcQuad s) hA
        _ = 6 * M * K s := cellInt_const_mul _ _
    rw [e1, e2, sub_zero]
    exact e3
  -- Grönwall: the cell energy of the difference is dominated by `K 0 · e^{6Ms}`
  have hDnn : ∀ s : ℝ, 0 ≤ cellInt (fun x => gradSq (fun a w => V w a - V' w a) (s, x)) :=
    fun s => cellInt_nonneg fun x => gradSq_nonneg _ _
  have hKnn : ∀ s : ℝ, 0 ≤ K s := fun s => cellInt_nonneg fun x =>
    mul_nonneg (by norm_num) (Finset.sum_nonneg fun a _ => mul_self_nonneg _)
  have hK0 : K 0 = 0 := by
    have hz : ∀ x : E3, quad (fun a w => V w a - V' w a) ((0 : ℝ), x) = 0 := by
      intro x
      have h1 : ∀ a : Fin 3, V ((0 : ℝ), x) a - V' ((0 : ℝ), x) a = 0 := by
        intro a; rw [hinit x]; ring
      have h2 : ∑ a, (V ((0 : ℝ), x) a - V' ((0 : ℝ), x) a)
          * (V ((0 : ℝ), x) a - V' ((0 : ℝ), x) a) = 0 :=
        Finset.sum_eq_zero fun a _ => by rw [h1 a]; ring
      have h3 : quad (fun a w => V w a - V' w a) ((0 : ℝ), x)
          = (1 / 2 : ℝ) * ∑ a, (V ((0 : ℝ), x) a - V' ((0 : ℝ), x) a)
              * (V ((0 : ℝ), x) a - V' ((0 : ℝ), x) a) := rfl
      rw [h3, h2, mul_zero]
    have hz' : K 0 = cellInt (fun _ : E3 => (0 : ℝ)) := by
      rw [hK]; exact cellInt_congr hz
    rw [hz']
    simp [cellInt]
  have hKdiff : ∀ s : ℝ, DifferentiableAt ℝ K s := fun s =>
    (hasDerivAt_cellInt (quad (fun a w => V w a - V' w a))
      (contDiff_quad _ hWsmooth) s).differentiableAt
  have hkey : ∀ s : ℝ, 0 ≤ s → s < T → ∃ d : ℝ, HasDerivAt K d s ∧ d ≤ 6 * M * K s := by
    intro s hs hsT
    refine ⟨_, hbal s hs hsT, ?_⟩
    have h1 := hsrc s hs hsT
    have h2 : 0 ≤ nu * cellInt (fun x => gradSq (fun a w => V w a - V' w a) (s, x)) :=
      mul_nonneg hnu (hDnn s)
    linarith
  have hexp : ∀ s : ℝ, HasDerivAt (fun r : ℝ => Real.exp (-(6 * M * r)))
      (Real.exp (-(6 * M * s)) * (-(6 * M))) s := by
    intro s
    have hlin : HasDerivAt (fun r : ℝ => -(6 * M * r)) (-(6 * M)) s := by
      simpa using ((hasDerivAt_id s).const_mul (6 * M)).neg
    exact (Real.hasDerivAt_exp (-(6 * M * s))).comp s hlin
  set g : ℝ → ℝ := fun s => K s * Real.exp (-(6 * M * s)) with hg
  have hgdiff : ∀ s : ℝ, DifferentiableAt ℝ g s := fun s =>
    (hKdiff s).mul (hexp s).differentiableAt
  have hgderiv : ∀ s : ℝ, 0 ≤ s → s < T → deriv g s ≤ 0 := by
    intro s hs hsT
    obtain ⟨d, hd, hle⟩ := hkey s hs hsT
    have hdg : HasDerivAt g (d * Real.exp (-(6 * M * s))
        + K s * (Real.exp (-(6 * M * s)) * (-(6 * M)))) s := hd.mul (hexp s)
    rw [hdg.deriv]
    have hE : (0 : ℝ) < Real.exp (-(6 * M * s)) := Real.exp_pos _
    have h3 : d * Real.exp (-(6 * M * s)) ≤ (6 * M * K s) * Real.exp (-(6 * M * s)) :=
      mul_le_mul_of_nonneg_right hle hE.le
    nlinarith [h3]
  have hanti : AntitoneOn g (Set.Icc 0 t) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 t)
      (fun s _ => (hgdiff s).continuousAt.continuousWithinAt)
      (fun s _ => (hgdiff s).differentiableWithinAt) ?_
    intro s hsint
    rw [interior_Icc] at hsint
    exact hgderiv s hsint.1.le (hsint.2.trans htT)
  have hgt : g t ≤ g 0 := hanti (Set.left_mem_Icc.mpr ht) (Set.right_mem_Icc.mpr ht) ht
  have hg0 : g 0 = 0 := by rw [hg]; simp [hK0]
  have hgtnn : 0 ≤ g t := by
    rw [hg]; exact mul_nonneg (hKnn t) (Real.exp_pos _).le
  have hzero : K t * Real.exp (-(6 * M * t)) = 0 := by
    have : g t = 0 := le_antisymm (hgt.trans_eq hg0) hgtnn
    rw [hg] at this
    exact this
  rcases mul_eq_zero.mp hzero with h | h
  · exact h
  · exact absurd h (ne_of_gt (Real.exp_pos _))

/-! ## Pointwise uniqueness on the window -/

/-- **Uniqueness of window solutions.**  Two smooth periodic divergence-free
solutions on `[0,T)` with the same initial velocity agree at every point of the
window.  No gradient bound is assumed: it is produced by compactness of the
torus. -/
theorem velocity_eq_of_same_datum_on (nu T : ℝ) (V V' : STime → E3) (P P' : STime → ℝ)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hV' : ContDiff ℝ (⊤ : ℕ∞) V')
    (hP : ContDiff ℝ (⊤ : ℕ∞) P) (hP' : ContDiff ℝ (⊤ : ℕ∞) P')
    (hVper : SpacePeriodic V) (hV'per : SpacePeriodic V')
    (hPper : SpacePeriodic P) (hP'per : SpacePeriodic P')
    (hnu : 0 ≤ nu)
    (hdiv : ∀ z : STime, 0 ≤ z.1 → z.1 < T → divg V z = 0)
    (hdiv' : ∀ z : STime, 0 ≤ z.1 → z.1 < T → divg V' z = 0)
    (hmom : ∀ z : STime, 0 ≤ z.1 → z.1 < T →
      dtime V z + adv V z = - grad P z + nu • lap V z)
    (hmom' : ∀ z : STime, 0 ≤ z.1 → z.1 < T →
      dtime V' z + adv V' z = - grad P' z + nu • lap V' z)
    (hinit : ∀ x : E3, V (0, x) = V' (0, x))
    {t : ℝ} (ht : 0 ≤ t) (htT : t < T) (x : E3) :
    V (t, x) = V' (t, x) := by
  classical
  obtain ⟨M, hMbound⟩ := exists_gradient_bound_on_slab hV' hV'per T
  have hM : ∀ z : STime, 0 ≤ z.1 → z.1 < T → ∀ j a : Fin 3,
      |dvec (0, ee j) (fun w => V' w a) z| ≤ M := fun z hz hzT j a =>
    hMbound z ⟨hz, hzT.le⟩ j a
  have hVc : ∀ i : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun w => V w i) := fun i => contDiff_coord V hV i
  have hV'c : ∀ i : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun w => V' w i) :=
    fun i => contDiff_coord V' hV' i
  have hWsmooth : ∀ a : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun w => V w a - V' w a) :=
    fun a => (hVc a).sub (hV'c a)
  have hWper : ∀ a : Fin 3, SpacePeriodic (fun w => V w a - V' w a) := by
    intro a z j
    have h1 : V (z.1, z.2 + ee j) a = V z a := spacePeriodic_coord hVper a z j
    have h2 : V' (z.1, z.2 + ee j) a = V' z a := spacePeriodic_coord hV'per a z j
    show V (z.1, z.2 + ee j) a - V' (z.1, z.2 + ee j) a = V z a - V' z a
    rw [h1, h2]
  have hfc : Continuous (fun y : E3 => quad (fun a w => V w a - V' w a) (t, y)) :=
    continuous_time_slice (contDiff_quad _ hWsmooth).continuous t
  have hfnn : ∀ y : E3, 0 ≤ quad (fun a w => V w a - V' w a) (t, y) := fun y =>
    mul_nonneg (by norm_num) (Finset.sum_nonneg fun a _ => mul_self_nonneg _)
  have hfper : ∀ (y : E3) (j : Fin 3),
      quad (fun a w => V w a - V' w a) (t, y + ee j)
        = quad (fun a w => V w a - V' w a) (t, y) :=
    fun y j => spacePeriodic_quad hWper (t, y) j
  have hzero := difference_energy_zero_on nu M T V V' P P' hV hV' hP hP' hVper hV'per hPper hP'per
    hnu hdiv hdiv' hmom hmom' hM hinit ht htT
  have h0 : quad (fun a w => V w a - V' w a) (t, x) = 0 :=
    eq_zero_of_cellInt_eq_zero hfc hfnn hfper hzero x
  have h1 : (1 / 2 : ℝ) * ∑ a, (V (t, x) a - V' (t, x) a) * (V (t, x) a - V' (t, x) a) = 0 := h0
  have hsum : ∑ a, (V (t, x) a - V' (t, x) a) * (V (t, x) a - V' (t, x) a) = 0 := by linarith
  have ha : ∀ a : Fin 3, V (t, x) a = V' (t, x) a := by
    intro a
    have hz := (Finset.sum_eq_zero_iff_of_nonneg
      (fun b (_ : b ∈ Finset.univ) => mul_self_nonneg (V (t, x) b - V' (t, x) b))).mp hsum a
      (Finset.mem_univ a)
    have := mul_self_eq_zero.mp hz
    linarith
  ext a
  exact ha a

/-! ## The window uniqueness gate is discharged -/

/-- **`WindowUniquenessGate` holds.**  This removes one of the plumbing gates of
`OpenGates.lean` from the unresolved list. -/
theorem windowUniquenessGate_holds : WindowUniquenessGate := by
  intro nu hnu T _hT V V' P P' hsol hsol' hinit z hz hzT
  obtain ⟨t, x⟩ := z
  exact velocity_eq_of_same_datum_on nu T V V' P P'
    hsol.smoothVelocity hsol'.smoothVelocity hsol.smoothPressure hsol'.smoothPressure
    hsol.periodicVelocity hsol'.periodicVelocity hsol.periodicPressure hsol'.periodicPressure
    hnu.le hsol.incompressible hsol'.incompressible hsol.momentum hsol'.momentum hinit hz hzT x

end ClayNS
