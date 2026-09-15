/-
# A literal state with strictly positive dyadic critical production

The scaling no-go `no_subcubic_remainder_absorption` is conditional on a state
whose literal critical production is strictly positive.  This file discharges
that hypothesis with an explicit triad state, so the no-go is not vacuous — and,
in its own right, shows that the dyadic critical weight genuinely breaks the
energy neutrality of the truncated nonlinearity: with the constant weight the
production vanishes identically (`force_energy_neutral_of`), while with the
dyadic weight it does not.

The state is carried by the resonant triad

```text
p = (1,1,0)   u_p = (0,0,−1)          |p|_∞ = 1,  w(p) = 1
q = (2,0,0)   u_q = (0,−1,0)          |q|_∞ = 2,  w(q) = 2
k = p+q = (3,1,0)   u_k = (0,0,−i)    |k|_∞ = 3,  w(k) = 4
```

together with the conjugate amplitudes at `−p, −q, −k`.  Each amplitude is
transverse to its own wavevector, the field is real, and it is supported on the
six retained modes.
-/
import RequestProject.NavierStokes.CriticalProductionAbsorption

noncomputable section

open Finset

namespace ClayNS.Waleffe

/-! ## The triad and its amplitudes -/

def witP : Wave := ![1, 1, 0]
def witQ : Wave := ![2, 0, 0]
def witK : Wave := ![3, 1, 0]

def witModes : Finset Wave := {witP, -witP, witQ, -witQ, witK, -witK}

/-- The explicit triad state. -/
def witField : Wave → Fin 3 → ℂ := fun m =>
  if m = witP then ![0, 0, -1]
  else if m = -witP then ![0, 0, -1]
  else if m = witQ then ![0, -1, 0]
  else if m = -witQ then ![0, -1, 0]
  else if m = witK then ![0, 0, -Complex.I]
  else if m = -witK then ![0, 0, Complex.I]
  else 0

theorem sum_witModes {M : Type*} [AddCommMonoid M] (f : Wave → M) :
    ∑ m ∈ witModes, f m
      = f witP + f (-witP) + f witQ + f (-witQ) + f witK + f (-witK) := by
  unfold witModes
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  abel

/-! ## The witness is an admissible Galerkin state -/

/-- The witness field is supported on the six retained modes. -/
theorem witField_support {k : Wave} (h : k ∉ witModes) : witField k = 0 := by
  have h1 : k ≠ witP := fun hk => h (by rw [hk]; decide)
  have h2 : k ≠ -witP := fun hk => h (by rw [hk]; decide)
  have h3 : k ≠ witQ := fun hk => h (by rw [hk]; decide)
  have h4 : k ≠ -witQ := fun hk => h (by rw [hk]; decide)
  have h5 : k ≠ witK := fun hk => h (by rw [hk]; decide)
  have h6 : k ≠ -witK := fun hk => h (by rw [hk]; decide)
  simp [witField, h1, h2, h3, h4, h5, h6]

/-- Each amplitude is transverse to its own wavevector: the witness field is
divergence free. -/
theorem witField_transverse (k : Wave) : herm (wC k) (witField k) = 0 := by
  by_cases h1 : k = witP
  · subst h1; simp +decide [witField, herm, wC, witP, Fin.sum_univ_three]
  by_cases h2 : k = -witP
  · subst h2; simp +decide [witField, herm, wC, witP, Fin.sum_univ_three]
  by_cases h3 : k = witQ
  · subst h3; simp +decide [witField, herm, wC, witQ, Fin.sum_univ_three]
  by_cases h4 : k = -witQ
  · subst h4; simp +decide [witField, herm, wC, witQ, Fin.sum_univ_three]
  by_cases h5 : k = witK
  · subst h5; simp +decide [witField, herm, wC, witK, Fin.sum_univ_three]
  by_cases h6 : k = -witK
  · subst h6; simp +decide [witField, herm, wC, witK, Fin.sum_univ_three]
  · simp [witField, h1, h2, h3, h4, h5, h6, herm]

/-- The witness field satisfies the reality condition of a real velocity
field. -/
theorem witField_reality (k : Wave) (i : Fin 3) :
    witField (-k) i = (starRingEnd ℂ) (witField k i) := by
  by_cases h1 : k = witP
  · subst h1; fin_cases i <;> simp +decide [witField]
  by_cases h2 : k = -witP
  · subst h2; fin_cases i <;> simp +decide [witField]
  by_cases h3 : k = witQ
  · subst h3; fin_cases i <;> simp +decide [witField]
  by_cases h4 : k = -witQ
  · subst h4; fin_cases i <;> simp +decide [witField]
  by_cases h5 : k = witK
  · subst h5; fin_cases i <;> simp +decide [witField]
  by_cases h6 : k = -witK
  · subst h6; fin_cases i <;> simp +decide [witField]
  · have g1 : -k ≠ witP := fun hk => h2 (by rw [← hk, neg_neg])
    have g2 : -k ≠ -witP := fun hk => h1 (by simpa using congrArg Neg.neg hk)
    have g3 : -k ≠ witQ := fun hk => h4 (by rw [← hk, neg_neg])
    have g4 : -k ≠ -witQ := fun hk => h3 (by simpa using congrArg Neg.neg hk)
    have g5 : -k ≠ witK := fun hk => h6 (by rw [← hk, neg_neg])
    have g6 : -k ≠ -witK := fun hk => h5 (by simpa using congrArg Neg.neg hk)
    simp [witField, h1, h2, h3, h4, h5, h6, g1, g2, g3, g4, g5, g6]

/-! ## The three shell weights of the triad -/

theorem critWeight_one_one_zero : critWeight ![1, 1, 0] = 1 := by
  have h : Nat.clog 2 (waveMaxCoord ![1, 1, 0]) = 0 := by decide
  simp [critWeight, critShell, h]

theorem critWeight_neg_one_one_zero : critWeight ![-1, -1, 0] = 1 := by
  have h : Nat.clog 2 (waveMaxCoord ![-1, -1, 0]) = 0 := by decide
  simp [critWeight, critShell, h]

theorem critWeight_three_one_zero : critWeight ![3, 1, 0] = 4 := by
  have h : Nat.clog 2 (waveMaxCoord ![3, 1, 0]) = 2 := by decide
  simp [critWeight, critShell, h]
  norm_num

theorem critWeight_neg_three_one_zero : critWeight ![-3, -1, 0] = 4 := by
  have h : Nat.clog 2 (waveMaxCoord ![-3, -1, 0]) = 2 := by decide
  simp [critWeight, critShell, h]
  norm_num

/-- **The literal critical production of the triad state is `12`.**  With the
constant weight the same quantity is zero (energy neutrality); the dyadic
critical weight puts the surviving mass on the output shell `w(k) = 4` against
the input shell `w(p) = 1`. -/
theorem critProductionOf_witField : critProductionOf witModes witField = 12 := by
  simp +decide [critProductionOf, sum_witModes, modalForcing, leray, advection, herm, wC, wsq,
    witField, witP, witQ, witK, Fin.sum_univ_three]
  rw [critWeight_one_one_zero, critWeight_neg_one_one_zero, critWeight_three_one_zero,
    critWeight_neg_three_one_zero]
  norm_num

/-- **Cross-check: the same state is energy neutral.**  Evaluated independently
of the weighted computation, the *unweighted* production of the witness state is
zero, as the energy neutrality of the truncated nonlinearity requires.  The
difference between this and `critProductionOf_witField = 12` is entirely the
dyadic weight. -/
theorem witField_unweighted_neutral :
    ∑ k ∈ witModes, (herm (modalForcing witModes witField k) (witField k)).re = 0 := by
  simp +decide [sum_witModes, modalForcing, leray, advection, herm, wC, wsq,
    witField, witP, witQ, witK, Fin.sum_univ_three]

/-- The hypothesis of the S2b scaling no-go is inhabited. -/
theorem critProductionOf_witField_pos : 0 < critProductionOf witModes witField := by
  rw [critProductionOf_witField]; norm_num

/-- **The S2b no-go is not vacuous.**  For the explicit triad state, no
state-independent absorbed coefficient together with an at-most-quadratic
remainder dominates the literal critical production. -/
theorem no_subcubic_remainder_absorption_wit (a K : ℝ)
    (R : (Wave → Fin 3 → ℂ) → ℝ)
    (hR : ∀ c : ℝ, 1 ≤ c → R (scaleField c witField) ≤ K * c ^ 2) :
    ∃ c : ℝ, 1 ≤ c ∧
      a * critDissipationOf witModes (scaleField c witField) + R (scaleField c witField)
        < critProductionOf witModes (scaleField c witField) :=
  no_subcubic_remainder_absorption critProductionOf_witField_pos a K R hR

end ClayNS.Waleffe
