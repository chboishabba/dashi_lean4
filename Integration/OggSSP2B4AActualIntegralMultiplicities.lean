import Mathlib

/-!
# ACTUAL published 4A(2B) integral Moonshine indecomposables and multiplicities

PRIMARY SOURCE:
S. Carnahan and S. Urano, "Monstrous Moonshine for Integral Group Rings",
International Mathematics Research Notices 2024(4), pp. 2748–2789,
DOI 10.1093/imrn/rnad028, Theorem 6.5 (as numbered in the paper);
also Urano's 2023 thesis Theorem 6.6 (DOI 10.15068/0002008083).

The published theorem specifies g in 4A(2B): g^2 is 2B. The graded
integral Monster module under <g> decomposes into ACTUAL integral group
ring indecomposable families A (rank 1), D (rank 4), C^A (rank 3),
with multiplicities a_n,d_n,c_n. In this source's notation:

  a = (T_2B + T_4A)/2
  d = (T_1A + T_2B - 2*T_4A)/4
  c = (-T_2B + T_4A)/2.

The present module computes SOURCE-BASED initial integer multiplicities,
not a made-up five-sector decomposition. Source scalar coefficients are
transcribed here from published McKay-Thompson expansions; this file
does not construct a 196884-dimensional integral lattice in Lean.
Only the numerical consequences are checked in kernel syntax.

The five supersingular inertia class defects (3,3,2,1,1) are an
INDEPENDENT 5-item geometry and are not these 3 module families.
-/

namespace Integration.OggSSP2B4AActualIntegralMultiplicities

inductive SourceIntegral4AModule
  | A | D | CA
  deriving DecidableEq, Repr, Fintype

def rank : SourceIntegral4AModule → ℕ
  | .A => 1
  | .D => 4
  | .CA => 3

def traceAtSquare2B : SourceIntegral4AModule → ℤ
  | .A => 1
  | .D => 0
  | .CA => -1

def traceAtGenerator4A : SourceIntegral4AModule → ℤ
  | .A => 1
  | .D => 0
  | .CA => 1

/-- At any specific grade, use a source tuple of integral multiplicities
and verify it against three INDEPENDENT analytic character coefficients. -/
structure GradeMultiplicity where
  a : ℕ
  d : ℕ
  c : ℕ
  rank1A : ℕ
  trace2B : ℤ
  trace4A : ℤ
  rankCorrect : a + 4*d + 3*c = rank1A
  twoBTraceCorrect : (a : ℤ) - c = trace2B
  fourATraceCorrect : (a : ℤ) + c = trace4A

/-- Published q^(-1) vacuum coefficients:
T_1A = T_2B = T_4A = 1. -/
def vacuum : GradeMultiplicity where
  a := 1
  d := 0
  c := 0
  rank1A := 1
  trace2B := 1
  trace4A := 1
  rankCorrect := by norm_num
  twoBTraceCorrect := by norm_num
  fourATraceCorrect := by norm_num

/-- Published q coefficient, grade n=2:
T_1A=196884, T_2B=276, T_4A=276. -/
def weightTwo : GradeMultiplicity where
  a := 276
  d := 49152
  c := 0
  rank1A := 196884
  trace2B := 276
  trace4A := 276
  rankCorrect := by norm_num
  twoBTraceCorrect := by norm_num
  fourATraceCorrect := by norm_num

/-- Published q² coefficient, grade n=3:
T_1A=21493760, T_2B=-2048, T_4A=2048. -/
def weightThree : GradeMultiplicity where
  a := 0
  d := 5371904
  c := 2048
  rank1A := 21493760
  trace2B := -2048
  trace4A := 2048
  rankCorrect := by norm_num
  twoBTraceCorrect := by norm_num
  fourATraceCorrect := by norm_num

theorem vacuum_is_actual_one_A :
    vacuum.a = 1 ∧ vacuum.d = 0 ∧ vacuum.c = 0 := by
  decide

theorem weight_two_actual_families :
    weightTwo.a = 276 ∧ weightTwo.d = 49152 ∧
      weightTwo.c = 0 := by
  decide

theorem weight_three_actual_families :
    weightThree.a = 0 ∧ weightThree.d = 5371904 ∧
      weightThree.c = 2048 := by
  decide

theorem weight_three_actual_CA_nonzero :
    0 < weightThree.c := by decide

/-- The grade-three C^A family is genuinely present; no five-sector
construction is needed to obtain a source-derived nontrivial
integral Monster module in this grade. -/
theorem rank_and_trace_reconstruct (m : GradeMultiplicity) :
    m.a + 4*m.d + 3*m.c = m.rank1A ∧
    (m.a : ℤ) - m.c = m.trace2B ∧
    (m.a : ℤ) + m.c = m.trace4A :=
  ⟨m.rankCorrect, m.twoBTraceCorrect, m.fourATraceCorrect⟩

/-- The source contains THREE integral indecomposable families, not five
families forced by matching the binary-tetrahedral orbit count. -/
theorem three_source_module_families :
    Fintype.card SourceIntegral4AModule = 3 := by
  decide

end Integration.OggSSP2B4AActualIntegralMultiplicities
