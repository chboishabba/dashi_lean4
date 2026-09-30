import Integration.OggSSP2B4AActualIntegralMultiplicities
import Integration.OggSSP2BVacuumTateNormalization

/-!
# ACTUAL 4A(2B) restricted module Tate computation

External source: Carnahan–Urano, "Monstrous Moonshine for Integral Group
Rings", Lemma 6.4 and Theorem 6.5 (DOI 10.1093/imrn/rnad028).
For H=<g²>≅C2 and g in 4A(2B) the theorem's actual integral
indecomposables restrict as:

    A | H   = Z_trivial
    D | H   = Z[H] ⊕ Z[H]
    C^A | H = Z[H] ⊕ I_sign.

We calculate ordinary C2 Tate cohomology on these concrete integral
actions, then apply the independently sourced actual grade
multiplicities. The result is Hhat0 is (F2)^a, Hhat1 is (F2)^c,
with D Tate-acyclic, where a,d,c are the source multiplicities.

The same source-backed grade-three result is 2048 odd Tate *classes*,
NOT five pieces of lengths 3,3,2,1,1. Separately distinguishing five
geometric inertia sectors would need an actual fifth source coordinate.
-/

namespace Integration.OggSSP2BActualRestrictedTate

namespace M := Integration.OggSSP2B4AActualIntegralMultiplicities

def regularNorm (v : ℤ × ℤ) : ℤ × ℤ :=
  (v.1+v.2, v.1+v.2)

def regularDiff (v : ℤ × ℤ) : ℤ × ℤ :=
  (v.2-v.1, v.1-v.2)

theorem regular_fixed_is_norm
    (v : ℤ × ℤ) (hfixed : v.1 = v.2) :
    ∃ u : ℤ × ℤ, regularNorm u = v := by
  refine ⟨(v.1, 0), ?_⟩
  exact Prod.ext (by simp [regularNorm]) (by simp [regularNorm, hfixed])

theorem regular_norm_zero_is_diff
    (v : ℤ × ℤ) (hnorm : regularNorm v = (0,0)) :
    ∃ u : ℤ × ℤ, regularDiff u = v := by
  have hsum : v.1 + v.2 = 0 := by
    have ha := congrArg Prod.fst hnorm
    simpa [regularNorm] using ha
  refine ⟨(0,v.1), ?_⟩
  apply Prod.ext
  · simp [regularDiff]
  · simp [regularDiff]
    omega

theorem sign_has_no_fixed_nonzero (n : ℤ)
    (hfixed : -n = n) : n = 0 := by
  omega

theorem sign_norm_zero (n : ℤ) : n + (-n) = 0 := by ring

theorem sign_diff_is_even (n : ℤ) : -n-n = 2*(-n) := by ring

theorem sign_odd_class_not_coboundary :
    ¬ ∃ n : ℤ, -n-n=1 := by
  rintro ⟨n, hn⟩
  omega

theorem sign_even_class_is_coboundary
    (v k : ℤ) (hv : v=2*k) :
    ∃ n : ℤ, -n-n=v := by
  exact ⟨-k, by omega⟩

/-- These family-wise ordinary Tate dimensions are a consequence of
the cited source restrictions and the preceding explicit calculation:
A: (H0,H1)=(1,0), D:(0,0), CA:(0,1). -/
def perCopyH0 : M.SourceIntegral4AModule → ℕ
  | .A => 1
  | .D => 0
  | .CA => 0

def perCopyH1 : M.SourceIntegral4AModule → ℕ
  | .A => 0
  | .D => 0
  | .CA => 1

def gradeH0Length (m : M.GradeMultiplicity) : ℕ :=
  m.a * perCopyH0 .A + m.d * perCopyH0 .D +
    m.c * perCopyH0 .CA

def gradeH1Length (m : M.GradeMultiplicity) : ℕ :=
  m.a * perCopyH1 .A + m.d * perCopyH1 .D +
    m.c * perCopyH1 .CA

theorem gradeH0_eq_actual_source_A (m : M.GradeMultiplicity) :
    gradeH0Length m = m.a := by
  simp [gradeH0Length, perCopyH0]

theorem gradeH1_eq_actual_source_CA (m : M.GradeMultiplicity) :
    gradeH1Length m = m.c := by
  simp [gradeH1Length, perCopyH1]

theorem weight_zero_ordinary_tate_lengths :
    gradeH0Length M.vacuum = 1 ∧
    gradeH1Length M.vacuum = 0 := by
  decide

theorem weight_two_ordinary_tate_lengths :
    gradeH0Length M.weightTwo = 276 ∧
    gradeH1Length M.weightTwo = 0 := by
  decide

theorem weight_three_ordinary_tate_lengths :
    gradeH0Length M.weightThree = 0 ∧
    gradeH1Length M.weightThree = 2048 := by
  decide

/-- For these source grades the difference of ordinary Tate lengths
equals the weight's ACTUAL 2B trace. -/
theorem low_weight_tate_trace
    (m : M.GradeMultiplicity) :
    (gradeH0Length m : ℤ) - (gradeH1Length m : ℤ)
      = m.trace2B := by
  rw [gradeH0_eq_actual_source_A, gradeH1_eq_actual_source_CA]
  exact m.twoBTraceCorrect

end Integration.OggSSP2BActualRestrictedTate
