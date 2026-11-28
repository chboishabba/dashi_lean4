import Integration.Paper9HeckePoleRemoval

/-! SOURCE-WRITTEN, UNCOMPILED.
Finite remainder transport for the original normalized cusp unit.
The native integer packet and actual Taylor coefficients are NOT
assumed proved by the finite replay. No new Hecke carrier. -/
namespace Integration.Paper9HeckeFiniteRemainder

open Complex Filter
open scoped Topology BigOperators
open Integration.Paper9ActualJSourceJet
open Integration.Paper9DiscriminantUnitReflection
open Integration.Paper9HeckePoleRemoval

noncomputable section

-- The retained remainder is a germ, not an equality of finite samples.
def Rem (n : ℕ) (f g : ℂ → ℂ) : Prop :=
  ∃ r : ℂ → ℂ, ContinuousAt r 0 ∧
    ∀ᶠ z in 𝓝 (0 : ℂ), f z - g z = z^n * r z

theorem remRefl (n : ℕ) (f : ℂ → ℂ) : Rem n f f := by
  refine ⟨fun _ => 0, continuousAt_const, ?_⟩
  exact Filter.Eventually.of_forall (fun z => by simp)

theorem remSub (n : ℕ) (f g u v : ℂ → ℂ)
    (h : Rem n f g) (k : Rem n u v) :
    Rem n (fun z => f z - u z) (fun z => g z - v z) := by
  obtain ⟨r,hr,he⟩ := h
  obtain ⟨s,hs,hf⟩ := k
  refine ⟨fun z => r z - s z, hr.sub hs, ?_⟩
  filter_upwards [he,hf] with z a b
  linear_combination a - b

theorem remMul (n : ℕ) (f g u v : ℂ → ℂ)
    (hg : ContinuousAt g 0) (hu : ContinuousAt u 0)
    (h : Rem n f g) (k : Rem n u v) :
    Rem n (fun z => f z * u z) (fun z => g z * v z) := by
  obtain ⟨r,hr,he⟩ := h
  obtain ⟨s,hs,hf⟩ := k
  refine ⟨fun z => r z * u z + g z * s z,
    (hr.mul hu).add (hg.mul hs), ?_⟩
  filter_upwards [he,hf] with z a b
  linear_combination u z * a + g z * b

theorem remProd {ι : Type*} [DecidableEq ι] (n : ℕ)
    (s : Finset ι) (f g : ι → ℂ → ℂ)
    (hf : ∀ i ∈ s, ContinuousAt (f i) 0)
    (hg : ∀ i ∈ s, ContinuousAt (g i) 0)
    (he : ∀ i ∈ s, Rem n (f i) (g i)) :
    Rem n (fun z => ∏ i ∈ s, f i z) (fun z => ∏ i ∈ s, g i z) := by
  induction s using Finset.induction_on with
  | empty => simpa using remRefl n (fun _ => 1)
  | @insert i s hi ih =>
    have hs : ∀ j ∈ s, j ∈ insert i s := fun j hj =>
      Finset.mem_insert_of_mem hj
    have hp := ih (fun j hj => hf j (hs j hj))
      (fun j hj => hg j (hs j hj)) (fun j hj => he j (hs j hj))
    have hc : ContinuousAt (fun z => ∏ j ∈ s, f j z) 0 := by
      apply continuousAt_finset_prod
      intro j hj
      exact hf j (hs j hj)
    simpa only [Finset.prod_insert hi] using
      remMul n (f i) (g i) (fun z => ∏ j ∈ s, f j z)
        (fun z => ∏ j ∈ s, g j z)
        (hg i (Finset.mem_insert_self _ _)) hc
        (he i (Finset.mem_insert_self _ _)) hp

-- Composition with a ramified monomial preserves the exponent, and
-- retains the extra zero modes rather than assuming an inverse chart.
theorem remMonomial (n k : ℕ) (a : ℂ) (f g : ℂ → ℂ)
    (hk : 0 < k) (h : Rem n f g) :
    Rem (k*n) (fun z => f (a*z^k)) (fun z => g (a*z^k)) := by
  obtain ⟨r,hr,he⟩ := h
  have hc : ContinuousAt (fun z : ℂ => a*z^k) 0 :=
    continuousAt_const.mul (continuousAt_id.pow k)
  have hz : a*(0:ℂ)^k=0 := by simp [zero_pow (Nat.ne_of_gt hk)]
  refine ⟨fun z => a^n*r (a*z^k), ?_, ?_⟩
  · exact continuousAt_const.mul (hr.comp_of_eq hc hz)
  · have ht : Tendsto (fun z : ℂ => a*z^k) (𝓝 0) (𝓝 0) := by
      simpa [hz] using hc.tendsto
    filter_upwards [ht.eventually he] with z h'
    dsimp at h' ⊢
    rw [h',mul_pow,pow_mul]
    ring

theorem remWeaken (n m : ℕ) (f g : ℂ → ℂ) (hm : m ≤ n)
    (h : Rem n f g) : Rem m f g := by
  obtain ⟨r,hr,he⟩ := h
  refine ⟨fun z => z^(n-m)*r z, (continuousAt_id.pow _).mul hr, ?_⟩
  filter_upwards [he] with z hz
  rw [hz, ← mul_assoc, ← pow_add, Nat.add_sub_of_le hm]

-- Use the actual formal discriminant unit J, not a fitted j-series.
def truncJ (m : ℕ) (z : ℂ) : ℂ :=
  ∑ i ∈ Finset.range (m+1), J.coeff i*z^i

def phase (a : Fin 41) : ℂ := Complex.exp (2*Real.pi*Complex.I*(a.val:ℂ)/41)

def diagonalNormalized (V : ℂ → ℂ) (z : ℂ) : ℂ :=
  ((z^41)^40*V (z^41)-V ((z^41)^41)) *
    ∏ a : Fin 41, (V (z^41)-(phase a*z)^40*V (phase a*z))

def sliceNormalized (V : ℂ → ℂ) (K z : ℂ) : ℂ :=
  (V ((z^41)^41)-K*(z^41)^41) *
    ∏ a : Fin 41, (V (phase a*z)-K*(phase a*z))

-- Normalized polynomial evaluation, valid even at z=0.
-- The packet supplies c in descending degree, including its constant.
def normalizedColumnEval (V : ℂ → ℂ) (d : ℕ) (c : ℕ → ℂ) (z : ℂ) : ℂ :=
  ∑ k ∈ Finset.range (d+1), c k * (z^41)^k * V (z^41)^(d-k)

-- If the actual finite polynomial residual is divisible at the required
-- order, the remaining analytic factor directly pays the old cusp
-- consumer. This is the final consumer, not a finite packet assertion.
theorem residualGermToCusp (n : ℕ) (f : UpperHalfPlane → ℂ)
    (A B : ℂ → ℂ) (h : Rem (n+1) A B)
    (he : ∀ᶠ τ in UpperHalfPlane.atImInfty,
      tParam τ^n * f τ = A (tParam τ)-B (tParam τ)) :
    IsZeroAtImInfty f := by
  obtain ⟨r,hr,hh⟩ := h
  apply normalizedResidualZero n f r hr
  filter_upwards [he,tTendsto.eventually hh] with τ a b
  exact a.trans b

-- Whole Hecke geometry from TWO actual ramified normalized finite germs.
-- The global modular rigidity (invariantZero) and original cusp removal
-- have ALREADY been proved in Paper9HeckePoleRemoval. This theorem
-- combines them and isolates precisely the new coefficient/analytic
-- producer `Rem` on each original normalized residual.
-- No freely chosen complex meromorphic substitute, no cusp-only
-- inference, and no asserted fixed j equality.
theorem bothActualHeckeIdentitiesFromRamifiedGerms
    (P : Polynomial ℂ) (K : ℂ)
    (diagUnit diagPacket sliceUnit slicePacket : ℂ → ℂ)
    (hd : Rem 3363 diagUnit diagPacket)
    (hs : Rem 1723 sliceUnit slicePacket)
    (hdiag : ∀ᶠ τ in UpperHalfPlane.atImInfty,
      tParam τ^3362 * diagonalResidual P τ =
        diagUnit (tParam τ) - diagPacket (tParam τ))
    (hslice : ∀ᶠ τ in UpperHalfPlane.atImInfty,
      tParam τ^1722 * sliceResidual K P τ =
        sliceUnit (tParam τ) - slicePacket (tParam τ)) :
    (∀ τ, actualProduct τ (j τ) = P.eval (j τ)) ∧
    (∀ τ, actualProduct τ K = P.eval (j τ)) := by
  have hzD : IsZeroAtImInfty (diagonalResidual P) :=
    residualGermToCusp 3362 (diagonalResidual P)
      diagUnit diagPacket hd hdiag
  have hzS : IsZeroAtImInfty (sliceResidual K P) :=
    residualGermToCusp 1722 (sliceResidual K P)
      sliceUnit slicePacket hs hslice
  exact ⟨diagonalIdentity P hzD, sliceIdentity K P hzS⟩

theorem actualCMPolynomialRootFromRamifiedGerms
    (P : Polynomial ℂ)
    (diagUnit diagPacket : ℂ → ℂ)
    (hd : Rem 3363 diagUnit diagPacket)
    (hdiag : ∀ᶠ τ in UpperHalfPlane.atImInfty,
      tParam τ^3362 * diagonalResidual P τ =
        diagUnit (tParam τ) - diagPacket (tParam τ)) :
    P.eval (j Integration.Paper9ActualCMPoint.cmTau) = 0 := by
  have hz : IsZeroAtImInfty (diagonalResidual P) :=
    residualGermToCusp 3362 (diagonalResidual P)
      diagUnit diagPacket hd hdiag
  exact actualCMDiagonalRoot P hz

end
end Integration.Paper9HeckeFiniteRemainder
