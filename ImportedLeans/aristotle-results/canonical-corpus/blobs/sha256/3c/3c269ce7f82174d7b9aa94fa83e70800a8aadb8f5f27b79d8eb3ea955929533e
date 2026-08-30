/-
# Uniqueness of smooth periodic solutions with bounded velocity gradient.

Fefferman's periodic alternative (B) does not ask for uniqueness, but every
continuation and compactness argument in the ladder silently uses it.  Here it
is derived, by the energy method, from the machinery of this development:

* `ClayNS.difference_transport` — the difference `w = u - v` of two solutions is
  transported by `u` with source `-(w·∇)v - ∇(p - q)`;
* `ClayNS.difference_energy_zero` — if `v` has a bounded velocity gradient and
  the two data agree, the cell energy of `w` vanishes for every `t ≥ 0`
  (Grönwall);
* `ClayNS.velocity_eq_of_same_datum` — hence the two velocity fields agree at
  every point of space, for every `t ≥ 0`.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.CellVanishing
import RequestProject.NavierStokes.Continuation

open scoped BigOperators
open MeasureTheory Set

noncomputable section

namespace ClayNS

/-! ## The difference of two solutions -/

lemma divg_sub (V V' : STime → E3) (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hV' : ContDiff ℝ (⊤ : ℕ∞) V')
    (z : STime) : divg (fun w => V w - V' w) z = divg V z - divg V' z := by
  have hsub : ContDiff ℝ (⊤ : ℕ∞) (fun w => V w - V' w) := hV.sub hV'
  rw [divg_eq_sum _ hsub z, divg_eq_sum V hV z, divg_eq_sum V' hV' z, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hcoord : (fun w : STime => (V w - V' w) i) = fun w => V w i - V' w i := rfl
  rw [hcoord]
  exact dvec_sub _ _ z ((differentiable_of_contDiffTop (contDiff_coord V hV i)) z)
    ((differentiable_of_contDiffTop (contDiff_coord V' hV' i)) z) (0, ee i)

/-- **Transport equation for the difference of two solutions.**  If `(u,p)` and
`(v,q)` both solve Navier–Stokes with viscosity `ν`, the difference
`w = u - v` satisfies

`∂_t w_a + (u·∇)w_a = -(w·∇)v_a - ∂_a(p-q) + ν Δw_a`. -/
theorem difference_transport (nu : ℝ) (V V' : STime → E3) (P P' : STime → ℝ)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hV' : ContDiff ℝ (⊤ : ℕ∞) V')
    (hP : ContDiff ℝ (⊤ : ℕ∞) P) (hP' : ContDiff ℝ (⊤ : ℕ∞) P')
    (a : Fin 3) (z : STime)
    (hmom : dtime V z + adv V z = - grad P z + nu • lap V z)
    (hmom' : dtime V' z + adv V' z = - grad P' z + nu • lap V' z) :
    dvec (1, 0) (fun w => V w a - V' w a) z
        + ∑ j, V z j * dvec (0, ee j) (fun w => V w a - V' w a) z
      = (-(∑ j, (V z j - V' z j) * dvec (0, ee j) (fun w => V' w a) z)
          - dvec (0, ee a) (fun w => P w - P' w) z)
        + nu * ∑ k, dvec (0, ee k) (dvec (0, ee k) (fun w => V w a - V' w a)) z := by
  have hVc : ∀ i : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun w => V w i) := fun i => contDiff_coord V hV i
  have hV'c : ∀ i : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun w => V' w i) :=
    fun i => contDiff_coord V' hV' i
  have hVd : ∀ i : Fin 3, Differentiable ℝ (fun w => V w i) := fun i =>
    differentiable_of_contDiffTop (hVc i)
  have hV'd : ∀ i : Fin 3, Differentiable ℝ (fun w => V' w i) := fun i =>
    differentiable_of_contDiffTop (hV'c i)
  have hmomc := momentum_component_at nu V P hV a z hmom
  have hmomc' := momentum_component_at nu V' P' hV' a z hmom'
  -- split all the derivatives of the difference
  have hsplit1 : dvec (1, 0) (fun w => V w a - V' w a) z
      = dvec (1, 0) (fun w => V w a) z - dvec (1, 0) (fun w => V' w a) z :=
    dvec_sub _ _ z ((hVd a) z) ((hV'd a) z) (1, 0)
  have hsplitj : ∀ j : Fin 3, dvec (0, ee j) (fun w => V w a - V' w a) z
      = dvec (0, ee j) (fun w => V w a) z - dvec (0, ee j) (fun w => V' w a) z :=
    fun j => dvec_sub _ _ z ((hVd a) z) ((hV'd a) z) (0, ee j)
  have hsplitP : dvec (0, ee a) (fun w => P w - P' w) z
      = dvec (0, ee a) P z - dvec (0, ee a) P' z :=
    dvec_sub _ _ z ((differentiable_of_contDiffTop hP) z)
      ((differentiable_of_contDiffTop hP') z) (0, ee a)
  have hsplitk : ∀ k : Fin 3, dvec (0, ee k) (dvec (0, ee k) (fun w => V w a - V' w a)) z
      = dvec (0, ee k) (dvec (0, ee k) (fun w => V w a)) z
        - dvec (0, ee k) (dvec (0, ee k) (fun w => V' w a)) z := by
    intro k
    have hfun : dvec (0, ee k) (fun w => V w a - V' w a)
        = fun w => dvec (0, ee k) (fun y => V y a) w - dvec (0, ee k) (fun y => V' y a) w :=
      dvec_sub_fun _ _ (hVd a) (hV'd a) (0, ee k)
    rw [hfun]
    exact dvec_sub _ _ z
      ((differentiable_of_contDiffTop (contDiff_dvec _ (hVc a) (0, ee k))) z)
      ((differentiable_of_contDiffTop (contDiff_dvec _ (hV'c a) (0, ee k))) z) (0, ee k)
  -- rewrite the two advection sums
  have hadv : (∑ j, V z j * dvec (0, ee j) (fun w => V w a - V' w a) z)
      + ∑ j, (V z j - V' z j) * dvec (0, ee j) (fun w => V' w a) z
      = (∑ j, V z j * dvec (0, ee j) (fun w => V w a) z)
        - ∑ j, V' z j * dvec (0, ee j) (fun w => V' w a) z := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hsplitj j]
    ring
  have hlap : ∑ k, dvec (0, ee k) (dvec (0, ee k) (fun w => V w a - V' w a)) z
      = (∑ k, dvec (0, ee k) (dvec (0, ee k) (fun w => V w a)) z)
        - ∑ k, dvec (0, ee k) (dvec (0, ee k) (fun w => V' w a)) z := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => hsplitk k
  rw [hsplit1, hsplitP, hlap]
  have hadv' := hadv
  rw [Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => congrArg (fun r => V z j * r)
    (hsplitj j))] at hadv'
  simp only [mul_sub] at hadv'
  rw [Finset.sum_sub_distrib] at hadv'
  linarith [hmomc, hmomc', hadv']

/-! ## Vanishing of the energy of the difference -/

/-- **Uniqueness in the energy norm.**  If `(u,p)` and `(v,q)` are smooth
periodic divergence-free solutions with the same viscosity and the same initial
velocity, and if the velocity gradient of `v` is bounded by `M`, then the cell
energy of `u - v` vanishes for every `t ≥ 0`. -/
theorem difference_energy_zero (nu M : ℝ) (V V' : STime → E3) (P P' : STime → ℝ)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hV' : ContDiff ℝ (⊤ : ℕ∞) V')
    (hP : ContDiff ℝ (⊤ : ℕ∞) P) (hP' : ContDiff ℝ (⊤ : ℕ∞) P')
    (hVper : SpacePeriodic V) (hV'per : SpacePeriodic V')
    (hPper : SpacePeriodic P) (hP'per : SpacePeriodic P')
    (hnu : 0 ≤ nu)
    (hdiv : ∀ w : STime, divg V w = 0) (hdiv' : ∀ w : STime, divg V' w = 0)
    (hmom : ∀ w : STime, dtime V w + adv V w = - grad P w + nu • lap V w)
    (hmom' : ∀ w : STime, dtime V' w + adv V' w = - grad P' w + nu • lap V' w)
    (hM : ∀ (z : STime) (j a : Fin 3), |dvec (0, ee j) (fun w => V' w a) z| ≤ M)
    (hinit : ∀ x : E3, V (0, x) = V' (0, x))
    {t : ℝ} (ht : 0 ≤ t) :
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
  have hWvdiv : ∀ w : STime, divg (fun y => V y - V' y) w = 0 := by
    intro w
    rw [divg_sub V V' hV hV' w, hdiv w, hdiv' w, sub_zero]
  -- the global balance for the difference
  have hbal := global_quadratic_balance nu V (fun a w => V w a - V' w a)
    (fun a w => -(∑ j, (V w j - V' w j) * dvec (0, ee j) (fun y => V' y a) w)
      - dvec (0, ee a) (fun y => P y - P' y) w)
    hV hVper hdiv hWsmooth hWper
    (fun a z => difference_transport nu V V' P P' hV hV' hP hP' a z (hmom z) (hmom' z))
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
  have hsrc : ∀ s : ℝ, cellInt (fun x => ∑ a, (V (s, x) a - V' (s, x) a)
        * (-(∑ j, (V (s, x) j - V' (s, x) j) * dvec (0, ee j) (fun y => V' y a) (s, x))
            - dvec (0, ee a) (fun y => P y - P' y) (s, x)))
      ≤ 6 * M * K s := by
    intro s
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
      have h0 := cellInt_pressure_work_eq_zero (fun w => V w - V' w) (fun w => P w - P' w)
        hWv hQ hWvper hQper hWvdiv s
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
          (fun j a => by rw [abs_neg]; exact hM (s, x) j a)
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
  have hkey : ∀ s : ℝ, ∃ d : ℝ, HasDerivAt K d s ∧ d ≤ 6 * M * K s := by
    intro s
    refine ⟨_, hbal s, ?_⟩
    have h1 := hsrc s
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
  have hgderiv : ∀ s : ℝ, ∃ d : ℝ, HasDerivAt g d s ∧ d ≤ 0 := by
    intro s
    obtain ⟨d, hd, hle⟩ := hkey s
    refine ⟨d * Real.exp (-(6 * M * s))
      + K s * (Real.exp (-(6 * M * s)) * (-(6 * M))), hd.mul (hexp s), ?_⟩
    have hE : (0 : ℝ) < Real.exp (-(6 * M * s)) := Real.exp_pos _
    have h3 : d * Real.exp (-(6 * M * s)) ≤ (6 * M * K s) * Real.exp (-(6 * M * s)) :=
      mul_le_mul_of_nonneg_right hle hE.le
    nlinarith [h3]
  have hganti : Antitone g :=
    antitone_of_deriv_nonpos (fun s => (hgderiv s).choose_spec.1.differentiableAt)
      (fun s => by
        obtain ⟨d, hd, hle⟩ := hgderiv s
        rw [hd.deriv]; exact hle)
  have hgt : g t ≤ g 0 := hganti ht
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

/-! ## Pointwise uniqueness -/

/-- **Uniqueness of smooth periodic solutions with bounded velocity gradient.**
Two smooth periodic divergence-free solutions of the Navier–Stokes system with
the same viscosity and the same initial velocity coincide at every point of
space, for every `t ≥ 0`, provided one of them has a bounded velocity
gradient. -/
theorem velocity_eq_of_same_datum (nu M : ℝ) (V V' : STime → E3) (P P' : STime → ℝ)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hV' : ContDiff ℝ (⊤ : ℕ∞) V')
    (hP : ContDiff ℝ (⊤ : ℕ∞) P) (hP' : ContDiff ℝ (⊤ : ℕ∞) P')
    (hVper : SpacePeriodic V) (hV'per : SpacePeriodic V')
    (hPper : SpacePeriodic P) (hP'per : SpacePeriodic P')
    (hnu : 0 ≤ nu)
    (hdiv : ∀ w : STime, divg V w = 0) (hdiv' : ∀ w : STime, divg V' w = 0)
    (hmom : ∀ w : STime, dtime V w + adv V w = - grad P w + nu • lap V w)
    (hmom' : ∀ w : STime, dtime V' w + adv V' w = - grad P' w + nu • lap V' w)
    (hM : ∀ (z : STime) (j a : Fin 3), |dvec (0, ee j) (fun w => V' w a) z| ≤ M)
    (hinit : ∀ x : E3, V (0, x) = V' (0, x))
    {t : ℝ} (ht : 0 ≤ t) (x : E3) :
    V (t, x) = V' (t, x) := by
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
  have hzero := difference_energy_zero nu M V V' P P' hV hV' hP hP' hVper hV'per hPper hP'per
    hnu hdiv hdiv' hmom hmom' hM hinit ht
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

end ClayNS
