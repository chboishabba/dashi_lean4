import Synthesis.NavierStokesActualEnergyBallContinuationExact

/-!
R30 actual arbitrary forward horizon at every FIXED cutoff.
Uniform restart radius on the original initial energy sublevel.
Build growing compatible trajectory charts; their evaluation glues
by clopen uniqueness on pairwise overlaps, not a new global choice
of initial data. The radius may depend on the cutoff and energy.
-/
namespace DASHI.NavierStokes.PhysicalMixed
open DASHI.NavierStokes.EuclideanMidpoint
open DASHI.NavierStokes.RealContinuation
open Set Filter MeasureTheory
open scoped Topology BigOperators
noncomputable section

theorem actual_global_forward_finite_flow (N : ℕ) (ν : ℝ) (hν : 0≤ν)
    (x₀ : FiniteState N)
    (hr : reflectState x₀=x₀)
    (ht : ∀ k,outputDot k (zeroExtend x₀ k)=0) :
    ∃ a<0,∃ X : ℝ → FiniteState N,
      X 0=x₀ ∧ SolvesOn (finiteForce N ν) X (Ioi a) ∧
      (∀ t≥0,reflectState (X t)=X t) ∧
      (∀ t≥0,∀ k,outputDot k (zeroExtend (X t) k)=0) ∧
      (∀ t≥0,stateEnergy (X t)+2*ν*(∫ s in 0..t,
        periodicDissipation N (fun k s=>zeroExtend (X s) k) s)=stateEnergy x₀) := by
  classical
  let F := finiteForce N ν
  have hF := finiteForce_contDiff N ν
  let K := energyBall N (stateEnergy x₀)
  have hK : IsCompact K := energyBall_compact N _ (stateEnergy_nonneg x₀)
  have hKne : K.Nonempty := ⟨x₀,le_rfl⟩
  obtain ⟨δ,hδ,H⟩ := compact_uniform_restart F hF K hK hKne
  obtain ⟨x,hx,ε,hε,hd⟩ := finite_local_solution N ν x₀
  let a := -ε
  let b : ℕ → ℝ := fun n=>ε+(n:ℝ)*(δ/2)
  have ha : a<0 := by dsimp [a]; linarith
  have hb (n : ℕ) : 0<b n := by dsimp [b]; positivity
  have hb_succ (n : ℕ) : b (n+1)=b n+δ/2 := by
    simp [b,Nat.cast_add]; ring
  have charts (n : ℕ) : ∃ y : ℝ → FiniteState N,
      y 0=x₀ ∧ SolvesOn F y (Ioo a (b n)) := by
    induction n with
    | zero => exact ⟨x,hx,by simpa [a,b,F,SolvesOn] using hd⟩
    | succ n ih =>
      obtain ⟨y,hy,hyODE⟩ := ih
      have htail (t : ℝ) (h : t∈Ioo 0 (b n)) : y t∈K := by
        have hh := forward_energy_bound N ν a (b n) hν y ha (hb n)
          (by rwa [hy]) (by rwa [hy]) hyODE t ⟨h.1.le,h.2⟩
        simpa [K,hy] using hh
      obtain ⟨z,hz,hagree⟩ := extend_with_restart_radius F hF y a 0 (b n)
        ha.le (hb n) hyODE K δ hδ H htail
      exact ⟨z,(hagree (show (0:ℝ)∈Ioo a (b n) from ⟨ha,hb n⟩)).trans hy,
        by rwa [hb_succ]⟩
  choose y hy hyODE using charts
  have hunbounded (t : ℝ) : ∃ n : ℕ,t<b n := by
    obtain ⟨n,hn⟩ := exists_nat_gt ((t-ε)/(δ/2))
    refine ⟨n,?_⟩
    have h := (div_lt_iff₀ (by positivity : 0<δ/2)).mp hn
    dsimp [b]
    linarith
  choose index hindex using hunbounded
  let X : ℝ → FiniteState N := fun t=>y (index t) t
  have hX0 : X 0=x₀ := hy (index 0)
  have hagree (n : ℕ) (t : ℝ) (h : t∈Ioo a (b n)) : X t=y n t := by
    let m := index t
    let I := Ioo a (min (b m) (b n))
    have hI (s : ℝ) (hs : s∈I) : s∈Ioo a (b m) ∧ s∈Ioo a (b n) :=
      ⟨⟨hs.1,hs.2.trans_le (min_le_left _ _)⟩,
        ⟨hs.1,hs.2.trans_le (min_le_right _ _)⟩⟩
    have he := agreement_on_connected F hF (y m) (y n)
      (I:=I) isOpen_Ioo (convex_Ioo _ _).isPreconnected
      (fun s hs=>hyODE m s (hI s hs).1)
      (fun s hs=>hyODE n s (hI s hs).2)
      0 ⟨ha,lt_min (hb m) (hb n)⟩ ((hy m).trans (hy n).symm)
    exact he (show t∈I from ⟨h.1,lt_min (hindex t) h.2⟩)
  have hXODE : SolvesOn F X (Ioi a) := by
    intro t ht'
    let n := index t
    have h : t∈Ioo a (b n) := ⟨ht',hindex t⟩
    have hev : X=ᶠ[𝓝 t] y n :=
      (isOpen_Ioo.mem_nhds h).mono fun s hs=>hagree n s hs
    rw [hagree n t h]
    exact (hyODE n t h).congr_of_eventuallyEq hev
  have hre (t : ℝ) (ht' : 0≤t) : reflectState (X t)=X t := by
    let n := index t
    have h := ⟨ha.trans_le ht',hindex t⟩
    rw [hagree n t h]
    exact reality_on_open_interval N ν a (b n) (y n) ha (hb n)
      (by rw [hy]; exact hr) (hyODE n) t h
  have htr (t : ℝ) (ht' : 0≤t) (k : Vec3) :
      outputDot k (zeroExtend (X t) k)=0 := by
    apply transverse_preserved N ν (fun k s=>zeroExtend (X s) k) t ht' k
    · rw [hX0]; exact ht k
    · intro s hs i
      exact zeroExtend_ODE_of_derivative N ν X s (hXODE s (ha.trans_le hs.1)) k i
  refine ⟨a,ha,X,hX0,hXODE,hre,htr,?_⟩
  intro t ht'
  let n := index t
  have hsol : SolvesOn F X (Ioo a (b n)) := fun s hs=>hXODE s hs.1
  have he := energy_on_forward_interval N ν a (b n) X ha (hb n)
    (by rw [hX0]; exact hr) (by rw [hX0]; exact ht)
    hsol t ⟨ht',hindex t⟩
  rwa [hX0] at he

end
end DASHI.NavierStokes.PhysicalMixed
