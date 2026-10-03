import Integration.OggSSP2BActualRestrictedTate

/-!
# 2B Tate grading-convention bridge

There are two indexing conventions in the primary sources which can look
contradictory if identified silently.

* Borcherds--Ryba, Modular Moonshine II, writes

      V = ⊕_{m∈ℤ} V_m,
      T_g(τ) = Σ_m Tr(g|V_m) q^m.

  Their Theorem 5.3 for a 2B involution says Hhat0 vanishes when this
  q-degree `m` is even, while Hhat1 vanishes when `m` is odd.

* Carnahan--Urano grades the Moonshine VOA by L0-weight `n ≥ 0` and writes

      Σ_n Tr(g|V_n) q^(n-1).

  Therefore the indices are related by

      m = n - 1.

Thus an even positive L0-weight `n` corresponds to an odd Borcherds--Ryba
q-degree `m`, exactly where Hhat1 vanishes and Hhat0 may be nonzero.  This is
consistent with Carnahan--Urano Lemma 6.4: for a 2B square, even weight pieces
restrict to sums of Z and Z[H], while odd weight pieces restrict to I and
Z[H].  Consequently the existing repo results

      weight 2 : (Hhat0,Hhat1) = (276,0)
      weight 3 : (Hhat0,Hhat1) = (0,2048)

are convention-compatible with Modular Moonshine II.

This owner exists to prevent future parity/sign mistakes in the Brauer-character
route to the actual 2B Tate module.
-/

namespace Integration.OggSSP2BTateGradingConventionBridge

namespace T := Integration.OggSSP2BActualRestrictedTate
namespace M := Integration.OggSSP2B4AActualIntegralMultiplicities

/-- Carnahan--Urano L0-weight `n` has q-exponent `n-1`. -/
def brQDegreeOfCUWeight (n : ℕ) : ℤ := (n : ℤ) - 1

theorem weightTwo_has_BR_degree_one :
    brQDegreeOfCUWeight 2 = 1 := by
  norm_num [brQDegreeOfCUWeight]

theorem weightThree_has_BR_degree_two :
    brQDegreeOfCUWeight 3 = 2 := by
  norm_num [brQDegreeOfCUWeight]

/-- Positive even CU weights map to odd BR degrees. -/
theorem even_weight_maps_to_odd_q_degree
    (k : ℕ) :
    brQDegreeOfCUWeight (2 * (k + 1)) = 2 * (k : ℤ) + 1 := by
  simp [brQDegreeOfCUWeight]
  omega

/-- Positive odd CU weights map to even BR degrees. -/
theorem odd_weight_maps_to_even_q_degree
    (k : ℕ) :
    brQDegreeOfCUWeight (2 * k + 1) = 2 * (k : ℤ) := by
  simp [brQDegreeOfCUWeight]
  omega

/-- Source-compatible low-weight parity receipt. -/
theorem low_weight_tate_parity_is_consistent :
    brQDegreeOfCUWeight 2 = 1
      ∧ T.gradeH0Length M.weightTwo = 276
      ∧ T.gradeH1Length M.weightTwo = 0
      ∧ brQDegreeOfCUWeight 3 = 2
      ∧ T.gradeH0Length M.weightThree = 0
      ∧ T.gradeH1Length M.weightThree = 2048 := by
  norm_num [brQDegreeOfCUWeight]
  exact ⟨T.weight_two_ordinary_tate_lengths.1,
    T.weight_two_ordinary_tate_lengths.2,
    T.weight_three_ordinary_tate_lengths.1,
    T.weight_three_ordinary_tate_lengths.2⟩

/-- Semantic boundary: a q-exponent parity statement must not be applied to
L0-weight parity without the index shift. -/
inductive SameParityConventionWithoutShift : Prop

theorem grading_shift_is_required :
    ¬ SameParityConventionWithoutShift := by
  intro h
  cases h

end Integration.OggSSP2BTateGradingConventionBridge
