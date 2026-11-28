import Synthesis.NavierStokesOriginalModalLimitEnergyInequalityExact

namespace DASHI.NavierStokes.PhysicalMixed
open DASHI.NavierStokes.EuclideanMidpoint
open DASHI.NavierStokes.RealContinuation
open Set Filter MeasureTheory
open scoped Topology BigOperators
noncomputable section

/-- Keep the original nonlinear modal equation and joint energy inequality
on one witness, without choosing a second diagonal subsequence. -/
theorem original_joint_modal_witness
    (ν B T : ℝ) (hν : 0<ν) (hB : 0≤B) (hT : 0≤T)
    (u₀ : Lattice → CVec3) (hmean : u₀ 0=0)
    (hr : ∀ k i,u₀ (-k) i=star (u₀ k i))
    (ht : ∀ k,outputDot (embedMode k) (u₀ k)=0)
    (hE : ∀ S : Finset Lattice,∑ k ∈ S,phaseMass (u₀ k)≤B) :
    ∃ V : Lattice → ℝ → CVec3,
      (∀ k,Continuous (V k)) ∧
      (∀ k,V k 0=u₀ k) ∧
      (∀ t∈Icc 0 T,V 0 t=0) ∧
      (∀ t∈Icc 0 T,∀ k,outputDot (embedMode k) (V k t)=0) ∧
      (∀ t∈Icc 0 T,∀ k i,V (-k) t i=star (V k t i)) ∧
      (∀ k ≠ 0,∀ i,∀ t∈Icc 0 T,
        V k t i=u₀ k i+(-((ν*massSq (embedMode k):ℝ):ℂ))*(∫ s in 0..t,V k s i)+
          ∫ s in 0..t,modeForceSeries k (fun p=>V p s) i) ∧
      (∀ t∈Icc 0 T,
        Summable (fun k=>phaseMass (V k t)) ∧
        Summable (fun k=>∫ s in 0..t,massSq (embedMode k)*phaseMass (V k s)) ∧
        (∑' k,phaseMass (V k t))+2*ν*(∑' k,∫ s in 0..t,
          massSq (embedMode k)*phaseMass (V k s))≤B) := by
  obtain ⟨X,σ,hσ,V,hx,hd,hv,hi,hEV,hconv,hm,htr,hreal,hs,he,hode⟩ :=
    original_periodic_modal_integral_limit ν B T hν hB hT u₀ hmean hr ht hE
  refine ⟨V,hv,hi,hm,htr,hreal,hode,?_⟩
  intro t ht'
  exact original_modal_limit_energy_inequality ν B T hν hB hT
    u₀ hr ht hE X hx hd σ V hconv t ht'

end
end DASHI.NavierStokes.PhysicalMixed
