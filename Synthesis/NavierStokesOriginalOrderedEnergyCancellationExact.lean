import Synthesis.NavierStokesLiteralGalerkinOutputFTCExact

/-!
Classical periodic Galerkin energy cancellation, on the original ordered
R30 fibre. The involution is (p,q,k) ↦ (-p,k,q), NOT the p/q swap
of the mixed helical carrier. Retain full conjugate-real phase.
-/
namespace DASHI.NavierStokes.PhysicalMixed
open DASHI.NavierStokes.EuclideanMidpoint
open scoped BigOperators
noncomputable section

def resonantPairs (N : ℕ) : Finset (Lattice × Lattice) :=
  ((cutoffModes N).product (cutoffModes N)).filter
    (fun a=>a.1+a.2∈cutoffModes N)

def energyFlip (a : Lattice × Lattice) : Lattice × Lattice :=
  (-a.1,a.1+a.2)

theorem energyFlip_involutive : Function.Involutive energyFlip := by
  intro a
  apply Prod.ext <;> simp [energyFlip]

theorem cutoff_neg (N : ℕ) (p : Lattice) (hp : p∈cutoffModes N) :
    -p∈cutoffModes N := by
  apply (mem_cutoffModes N _).mpr
  intro i
  have h := (mem_cutoffModes N p).mp hp i
  change -(N:ℤ)≤ -p i ∧ -p i≤(N:ℤ)
  omega

theorem energyFlip_mem (N : ℕ) (a : Lattice × Lattice)
    (ha : a∈resonantPairs N) : energyFlip a∈resonantPairs N := by
  simp only [resonantPairs,Finset.mem_filter,Finset.mem_product] at ha ⊢
  exact ⟨⟨cutoff_neg N a.1 ha.1.1,ha.2⟩,by simpa [energyFlip] using ha.1.2⟩

def physicalDot (u : Lattice → CVec3) (p q : Lattice) :=
  outputDot (embedMode q) (u p)

def rawEnergyCell (u : Lattice → CVec3) (a : Lattice × Lattice) : ℝ :=
  realHermitian
    (fun i=> -Complex.I * physicalDot u a.1 a.2 * u a.2 i)
    (u (a.1+a.2))

/-- Advective transfer is antisymmetric on the exact resonance orbit.
Conjugating the transporting mode is indispensable. -/
theorem rawEnergyCell_flip (u : Lattice → CVec3)
    (htrans : ∀ p,physicalDot u p p=0)
    (hreal : ∀ p i,u (-p) i=star (u p i)) (a : Lattice × Lattice) :
    rawEnergyCell u (energyFlip a) = -rawEnergyCell u a := by
  obtain ⟨p,q⟩ := a
  have hdot : physicalDot u (-p) (p+q)=star (physicalDot u p q) := by
    have hp := htrans p
    unfold physicalDot outputDot embedMode at hp ⊢
    rw [star_sum]
    simp only [Fin.sum_univ_three,hreal,Pi.add_apply,Int.cast_add,
      Complex.ofReal_add,star_add,star_mul,Complex.star_def,Complex.conj_ofReal]
    apply Complex.ext
    · have h := congrArg Complex.re hp
      simp [Complex.add_re,Complex.mul_re] at h ⊢
      linear_combination h
    · have h := congrArg Complex.im hp
      simp [Complex.add_im,Complex.mul_im] at h ⊢
      linear_combination -h
  unfold rawEnergyCell
  simp only [energyFlip,hdot,neg_add_cancel_left]
  simp [realHermitian,Fin.sum_univ_three,Complex.mul_re,Complex.mul_im,
    Complex.neg_re,Complex.neg_im] <;> ring

/-- Exact Leray removal against the transverse output test. -/
theorem orderedEnergyCell_eq_raw (u : Lattice → CVec3)
    (htrans : ∀ p,physicalDot u p p=0) (p q : Lattice) :
    realHermitian (orderedRHS (embedMode (p+q)) (embedMode q) (u p) (u q))
      (u (p+q))=rawEnergyCell u (p,q) := by
  have hp := htrans (p+q)
  have hr := congrArg Complex.re hp
  have hi := congrArg Complex.im hp
  let k := embedMode (p+q)
  let v : CVec3 := fun j=>outputDot (embedMode q) (u p)*u q j
  let w := u (p+q)
  have h : outputDot k w=0 := hp
  have hR := congrArg Complex.re h
  have hI := congrArg Complex.im h
  let z := outputDot k v
  change realHermitian (fun i=> -Complex.I*lerayVector k v i) w =
    realHermitian (fun i=> -Complex.I*v i) w
  unfold lerayVector realHermitian
  change (∑ i : Fin 3,((-Complex.I*(v i-(k i/massSq k : ℝ)*z)).re*(w i).re+
    (-Complex.I*(v i-(k i/massSq k : ℝ)*z)).im*(w i).im)) = _
  simp only [outputDot,Fin.sum_univ_three,Complex.add_re,Complex.add_im,
    Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im] at hR hI
  simp [Fin.sum_univ_three,Complex.mul_re,Complex.mul_im,Complex.sub_re,Complex.sub_im]
  ring_nf at hR hI ⊢
  linear_combination (norm := ring_nf)
    -(z.im/massSq k)*hR+(z.re/massSq k)*hI

theorem rawEnergyFold_zero (N : ℕ) (u : Lattice → CVec3)
    (htrans : ∀ p,physicalDot u p p=0)
    (hreal : ∀ p i,u (-p) i=star (u p i)) :
    (∑ a ∈ resonantPairs N,rawEnergyCell u a)=0 := by
  classical
  have he : (∑ a ∈ resonantPairs N,rawEnergyCell u a)=
      ∑ a ∈ resonantPairs N,-rawEnergyCell u a := by
    apply Finset.sum_nbij' energyFlip energyFlip
    · exact energyFlip_mem N
    · exact energyFlip_mem N
    · intro a _
      exact energyFlip_involutive a
    · intro a _
      exact energyFlip_involutive a
    · intro a _
      rw [rawEnergyCell_flip u htrans hreal,neg_neg]
  rw [Finset.sum_neg_distrib] at he
  linarith

theorem projectedEnergyFold_zero (N : ℕ) (u : Lattice → CVec3)
    (htrans : ∀ p,physicalDot u p p=0)
    (hreal : ∀ p i,u (-p) i=star (u p i)) :
    (∑ a ∈ resonantPairs N,
      realHermitian (orderedRHS (embedMode (a.1+a.2)) (embedMode a.2)
        (u a.1) (u a.2)) (u (a.1+a.2)))=0 := by
  simp_rw [orderedEnergyCell_eq_raw u htrans]
  exact rawEnergyFold_zero N u htrans hreal

/-- Reindex the exact original output fibre fold to the resonant-pair
carrier. The zero-output term is literally zero for mean-zero U. -/
theorem outputEnergyFold_zero (N : ℕ) (u : Lattice → CVec3)
    (htrans : ∀ p,physicalDot u p p=0)
    (hreal : ∀ p i,u (-p) i=star (u p i)) (hmean : u 0=0) :
    (∑ k ∈ outputModes N,∑ a ∈ orderedFibre N k,
      realHermitian (orderedRHS (embedMode k) (embedMode a.2) (u a.1) (u a.2))
        (u k))=0 := by
  classical
  let f := fun k a => realHermitian
    (orderedRHS (embedMode k) (embedMode a.2) (u a.1) (u a.2)) (u k)
  change (∑ k ∈ outputModes N,∑ a ∈ orderedFibre N k,f k a)=0
  have hzero : ∀ a, f 0 a=0 := by
    intro a
    simp [f,hmean,realHermitian]
  have hz : (∑ k ∈ outputModes N,∑ a ∈ orderedFibre N k,f k a)=
      ∑ k ∈ cutoffModes N,∑ a ∈ orderedFibre N k,f k a := by
    unfold outputModes
    by_cases h : (0:Lattice)∈cutoffModes N
    · rw [← Finset.sum_erase_add _ _ h]
      simp [hzero]
    · rw [Finset.erase_eq_of_notMem h]
  rw [hz]
  simp only [orderedFibre,Finset.sum_filter]
  rw [Finset.sum_comm]
  have hsingle (a : Lattice × Lattice) :
      (∑ k ∈ cutoffModes N,if a.1+a.2=k then f k a else 0)=
        if a.1+a.2∈cutoffModes N then f (a.1+a.2) a else 0 := by
    simp [eq_comm]
  simp_rw [hsingle]
  rw [← Finset.sum_filter]
  exact projectedEnergyFold_zero N u htrans hreal

end
end DASHI.NavierStokes.PhysicalMixed
