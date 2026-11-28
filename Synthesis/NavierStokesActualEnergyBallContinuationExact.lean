import Synthesis.NavierStokesClopenCompactContinuationExact

/-!
Literal finite physical energy ball, R27/R29/R30.
The energy is the sum on the original nonzero Fourier cutoff, not
a newly selected norm. The real state sublevel is compact for each
fixed N. This does not assert strong compactness as N tends to infinity.
-/
namespace DASHI.NavierStokes.PhysicalMixed
open DASHI.NavierStokes.EuclideanMidpoint
open DASHI.NavierStokes.RealContinuation
open MeasureTheory Set Metric
open scoped BigOperators Topology
noncomputable section

def stateEnergy {N : ℕ} (x : FiniteState N) : ℝ :=
  periodicEnergy N (fun k _=>zeroExtend x k) 0

theorem stateEnergy_nonneg {N : ℕ} (x : FiniteState N) : 0≤stateEnergy x := by
  unfold stateEnergy periodicEnergy realHermitian
  apply Finset.sum_nonneg
  intro k _
  apply Finset.sum_nonneg
  intro i _
  positivity

theorem stateEnergy_continuous (N : ℕ) : Continuous (@stateEnergy N) := by
  unfold stateEnergy periodicEnergy
  apply continuous_finset_sum
  intro k hk
  unfold realHermitian
  have h (i : Fin 3) : Continuous (fun x : FiniteState N=>zeroExtend x (embedMode k) i) :=
    (zeroExtend_contDiff N (embedMode k) i).continuous
  simp only [Fin.sum_univ_three]
  fun_prop

theorem coordinate_square_le_energy {N : ℕ} (x : FiniteState N)
    (p : Mode N) (i : Fin 3) : ‖x p i‖^2≤stateEnergy x := by
  rw [Complex.sq_norm,Complex.normSq_apply]
  have hm : (x p i).re*(x p i).re+(x p i).im*(x p i).im ≤
      realHermitian (x p) (x p) := by
    unfold realHermitian
    exact Finset.single_le_sum (fun j _=>by positivity) (Finset.mem_univ i)
  have hh : realHermitian (zeroExtend x (embedMode p.1))
      (zeroExtend x (embedMode p.1))≤stateEnergy x := by
    unfold stateEnergy periodicEnergy
    exact Finset.single_le_sum (fun k _=>by
      unfold realHermitian
      apply Finset.sum_nonneg
      intro j _
      positivity) p.2
  rw [zeroExtend_at] at hh
  exact hm.trans hh

theorem state_norm_le_of_energy {N : ℕ} (x : FiniteState N)
    (B : ℝ) (hB : 0≤B) (hx : stateEnergy x≤B) :
    ‖x‖≤Real.sqrt B := by
  apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg B)).mpr
  intro p
  apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg B)).mpr
  intro i
  have h := (coordinate_square_le_energy x p i).trans hx
  have hs := Real.sq_sqrt hB
  nlinarith [norm_nonneg (x p i),Real.sqrt_nonneg B]

def energyBall (N : ℕ) (B : ℝ) : Set (FiniteState N) :=
  {x | stateEnergy x≤B}

theorem energyBall_compact (N : ℕ) (B : ℝ) (hB : 0≤B) :
    IsCompact (energyBall N B) := by
  have hclosed : IsClosed (energyBall N B) :=
    isClosed_le (stateEnergy_continuous N) continuous_const
  apply (isCompact_closedBall (0:FiniteState N) (Real.sqrt B)).of_isClosed_subset hclosed
  intro x hx
  simpa [Metric.mem_closedBall,dist_zero_right] using
    state_norm_le_of_energy x B hB hx

/-- Reality on the entire open existence interval, not just a germ
near the initial point. The equality locus is the genuine relative
clopen set from the preceding module. -/
theorem reality_on_open_interval (N : ℕ) (ν a b : ℝ)
    (x : ℝ → FiniteState N) (ha : a<0) (hb : 0<b)
    (hr : reflectState (x 0)=x 0)
    (hd : SolvesOn (finiteForce N ν) x (Ioo a b)) :
    ∀ t∈Ioo a b,reflectState (x t)=x t := by
  let y : ℝ → FiniteState N := fun t=>reflectLinear N (x t)
  have hy : SolvesOn (finiteForce N ν) y (Ioo a b) := by
    intro t ht
    have h := (reflectLinear N).hasFDerivAt.comp_hasDerivAt (hd t ht)
    simpa [y,reflectLinear_apply,finiteForce_reflect] using h
  have he := agreement_on_connected (finiteForce N ν) (finiteForce_contDiff N ν)
    y x isOpen_Ioo (convex_Ioo _ _).isPreconnected hy hd 0 ⟨ha,hb⟩
    (by simpa [y,reflectLinear_apply] using hr)
  intro t ht
  simpa [y,reflectLinear_apply] using he ht

theorem energy_on_forward_interval (N : ℕ) (ν a b : ℝ)
    (x : ℝ → FiniteState N) (ha : a<0) (hb : 0<b)
    (hr : reflectState (x 0)=x 0)
    (htrans : ∀ k,outputDot k (zeroExtend (x 0) k)=0)
    (hd : SolvesOn (finiteForce N ν) x (Ioo a b))
    (t : ℝ) (ht : t∈Ico 0 b) :
    stateEnergy (x t)+2*ν*(∫ s in 0..t,
      periodicDissipation N (fun k s=>zeroExtend (x s) k) s)=stateEnergy (x 0) := by
  let U := fun k s=>zeroExtend (x s) k
  have hsub : uIcc 0 t⊆Ioo a b := by
    rw [uIcc_of_le ht.1]
    intro s hs
    exact ⟨ha.trans_le hs.1,hs.2.trans_lt ht.2⟩
  have ho (s : ℝ) (hs : s∈uIcc 0 t) (k : Vec3) (i : Fin 3) :
      HasDerivAt (fun r=>U k r i)
        (-((ν*massSq k:ℝ):ℂ)*U k s i+galerkinForce N U k s i) s :=
    zeroExtend_ODE_of_derivative N ν x s (hd s (hsub hs)) k i
  have hreal := reality_on_open_interval N ν a b x ha hb hr hd
  have h := periodic_energy_FTC_on_interval N ν U t
    (fun k i s hs=>(ho s hs k i).continuousAt.continuousWithinAt) ho
    (by
      intro s hs k
      have hs' : s∈Icc 0 t := by simpa [uIcc_of_le ht.1] using hs
      apply transverse_preserved N ν U s hs'.1 (embedMode k) (htrans _)
      intro r hr' i
      apply ho r _ (embedMode k) i
      rw [uIcc_of_le ht.1]
      exact ⟨hr'.1,hr'.2.trans hs'.2⟩)
    (by
      intro s hs k i
      have hh := zeroExtend_reflect (x s) (-k) i
      rw [hreal s (hsub hs),neg_neg] at hh
      exact hh)
    (fun s _=>zeroExtend_mean (x s))
  exact h

theorem forward_energy_bound (N : ℕ) (ν a b : ℝ) (hν : 0≤ν)
    (x : ℝ → FiniteState N) (ha : a<0) (hb : 0<b)
    (hr : reflectState (x 0)=x 0)
    (ht : ∀ k,outputDot k (zeroExtend (x 0) k)=0)
    (hd : SolvesOn (finiteForce N ν) x (Ioo a b))
    (t : ℝ) (h : t∈Ico 0 b) : x t∈energyBall N (stateEnergy (x 0)) := by
  have he := energy_on_forward_interval N ν a b x ha hb hr ht hd t h
  have hi := intervalIntegral.integral_nonneg_of_forall h.1
    (periodicDissipation_nonneg N (fun k s=>zeroExtend (x s) k))
  change stateEnergy (x t)≤stateEnergy (x 0)
  nlinarith [mul_nonneg hν hi]

/-- Actual same-trajectory extension at every finite forward endpoint.
The previously uninhabited finite escape reducer has a real analytic
consumer. Still no uniform critical-time estimate as N varies. -/
theorem actual_physical_forward_extension (N : ℕ) (ν a b : ℝ) (hν : 0≤ν)
    (x : ℝ → FiniteState N) (ha : a<0) (hb : 0<b)
    (hr : reflectState (x 0)=x 0)
    (ht : ∀ k,outputDot k (zeroExtend (x 0) k)=0)
    (hd : SolvesOn (finiteForce N ν) x (Ioo a b)) :
    ∃ c>b,∃ z : ℝ → FiniteState N,
      SolvesOn (finiteForce N ν) z (Ioo a c) ∧ EqOn z x (Ioo a b) := by
  apply extend_bounded_open_interval_tail (finiteForce N ν) (finiteForce_contDiff N ν)
    x a 0 b ha.le hb hd (energyBall N (stateEnergy (x 0)))
    (energyBall_compact N _ (stateEnergy_nonneg _))
  intro t h
  exact forward_energy_bound N ν a b hν x ha hb hr ht hd t ⟨h.1.le,h.2⟩

end
end DASHI.NavierStokes.PhysicalMixed
