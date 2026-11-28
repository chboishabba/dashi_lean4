import Synthesis.NavierStokesActualFractionalSignedFTCExact
import Synthesis.NavierStokesOriginalModalLimitEnergyInequalityExact

/-! Retain the signed weight difference on the original advective
involution instead of bounding each unpaired cell separately. This
is an exact source identity for the N2e transfer. It does not pay
the cutoff-uniform critical budget. -/
namespace DASHI.NavierStokes.PhysicalMixed
open DASHI.NavierStokes.EuclideanMidpoint
open scoped BigOperators
noncomputable section

theorem weighted_rawEnergyFold_flip (N : ℕ) (w : Lattice → ℝ)
    (u : Lattice → CVec3)
    (ht : ∀ p,physicalDot u p p=0)
    (hr : ∀ p i,u (-p) i=star (u p i)) :
    (∑ a ∈ resonantPairs N,w (a.1+a.2)*rawEnergyCell u a)=
      -(∑ a ∈ resonantPairs N,w a.2*rawEnergyCell u a) := by
  classical
  have h : (∑ a ∈ resonantPairs N,w (a.1+a.2)*rawEnergyCell u a)=
      ∑ a ∈ resonantPairs N,w a.2*(-rawEnergyCell u a) := by
    apply Finset.sum_nbij' energyFlip energyFlip
    · exact energyFlip_mem N
    · exact energyFlip_mem N
    · intro a _
      exact energyFlip_involutive a
    · intro a _
      exact energyFlip_involutive a
    · intro a _
      simp [energyFlip,rawEnergyCell_flip u ht hr]
  simpa [mul_neg,Finset.sum_neg_distrib] using h

theorem weighted_rawEnergyFold_commutator (N : ℕ) (w : Lattice → ℝ)
    (u : Lattice → CVec3)
    (ht : ∀ p,physicalDot u p p=0)
    (hr : ∀ p i,u (-p) i=star (u p i)) :
    2*(∑ a ∈ resonantPairs N,w (a.1+a.2)*rawEnergyCell u a)=
      ∑ a ∈ resonantPairs N,(w (a.1+a.2)-w a.2)*rawEnergyCell u a := by
  rw [show (∑ a ∈ resonantPairs N,(w (a.1+a.2)-w a.2)*rawEnergyCell u a)=
    (∑ a ∈ resonantPairs N,w (a.1+a.2)*rawEnergyCell u a)-
      (∑ a ∈ resonantPairs N,w a.2*rawEnergyCell u a) by
      simp_rw [sub_mul,Finset.sum_sub_distrib]]
  have h := weighted_rawEnergyFold_flip N w u ht hr
  linarith

/-- Reindex the literal weighted original force fold, preserving the
same input/output addresses and the mean-zero condition. -/
theorem actual_fractionalTransfer_commutator (N : ℕ) (w : Lattice → ℝ)
    (U : Vec3 → ℝ → CVec3) (t : ℝ)
    (ht : ∀ p,outputDot (embedMode p) (U (embedMode p) t)=0)
    (hr : ∀ p i,U (embedMode (-p)) t i=star (U (embedMode p) t i))
    (hm : U (embedMode 0) t=0) :
    fractionalTransfer N w U t=
      ∑ a ∈ resonantPairs N,(w (a.1+a.2)-w a.2)*
        rawEnergyCell (fun p=>U (embedMode p) t) a := by
  classical
  let u := fun p=>U (embedMode p) t
  let f := fun k a=>w k*realHermitian
    (orderedRHS (embedMode k) (embedMode a.2) (u a.1) (u a.2)) (u k)
  have hforce (k : Lattice) (hk : k∈outputModes N) :
      w k*realHermitian (galerkinForce N U (embedMode k) t) (u k)=
        ∑ a ∈ orderedFibre N k,f k a := by
    have he : galerkinForce N U (embedMode k) t =
        fun i=>∑ a ∈ orderedFibre N k,orderedRHS (embedMode k) (embedMode a.2)
          (u a.1) (u a.2) i := by
      funext i
      exact galerkinForce_eq_orderedFibre N U k hk t i
    rw [he,realHermitian_sum_left,Finset.mul_sum]
    rfl
  have hz : (∑ k ∈ outputModes N,∑ a ∈ orderedFibre N k,f k a)=
      ∑ k ∈ cutoffModes N,∑ a ∈ orderedFibre N k,f k a := by
    have h0 : (0:Lattice)∈cutoffModes N :=
      (mem_cutoffModes N 0).mpr (by intro i; simp)
    unfold outputModes
    rw [← Finset.sum_erase_add _ _ h0]
    simp [f,u,hm,realHermitian]
  unfold fractionalTransfer
  rw [show (∑ k ∈ outputModes N,w k*realHermitian (galerkinForce N U (embedMode k) t)
      (U (embedMode k) t))=∑ k ∈ outputModes N,∑ a ∈ orderedFibre N k,f k a from
        Finset.sum_congr rfl hforce,hz]
  simp only [orderedFibre,Finset.sum_filter]
  rw [Finset.sum_comm]
  have hsingle (a : Lattice × Lattice) :
      (∑ k ∈ cutoffModes N,if a.1+a.2=k then f k a else 0)=
        if a.1+a.2∈cutoffModes N then f (a.1+a.2) a else 0 := by simp [eq_comm]
  simp_rw [hsingle]
  rw [← Finset.sum_filter]
  change 2*(∑ a ∈ resonantPairs N,w (a.1+a.2)*realHermitian
    (orderedRHS (embedMode (a.1+a.2)) (embedMode a.2) (u a.1) (u a.2))
    (u (a.1+a.2)))=_
  simp_rw [orderedEnergyCell_eq_raw u ht]
  exact weighted_rawEnergyFold_commutator N w u ht hr

end
end DASHI.NavierStokes.PhysicalMixed
