import Jordan.AlbertAlgebra
import Integration.AlbertScalarTraceless
import Integration.AlbertJordanAutomorphism

/-!
# Standard real Albert adapter compatibility probe

This file is intentionally not imported by the ordinary DASHI rollup.  The
focused workflow exposes the exact pinned donor on `LEAN_PATH` and asks whether
this adapter compiles under the DASHI 4.35 kernel.

If GREEN, the previously external H3(O) artifact has crossed the same-kernel
compatibility seam.  Until then this is source-written port code only.
-/

namespace ExternalAlbert.RealAlbertAdapterProbe

open Integration.AlbertScalarTraceless
open Integration.AlbertJordanAutomorphism

abbrev RealAlbert := Octonion.AlbertAlgebra
  (R := ℝ) (a := (-1 : ℝ)) (b := (-1 : ℝ)) (c := (1 : ℝ))

def negOneRegular : ∀ x : ℝ, (-1 : ℝ) * x = 0 → x = 0 := by
  intro x h
  simpa using h

def oneRegular : ∀ x : ℝ, (1 : ℝ) * x = 0 → x = 0 := by
  intro x h
  simpa using h

noncomputable local instance realAlbertJordan : JordanAlgebra ℝ RealAlbert :=
  Octonion.ofAlbert
    (R := ℝ) (a := (-1 : ℝ)) (b := (-1 : ℝ)) (c := (1 : ℝ))
    negOneRegular negOneRegular oneRegular

noncomputable local instance realAlbertFormallyReal : IsFormallyReal ℝ RealAlbert :=
  Octonion.isFormallyReal
    (R := ℝ) (a := (-1 : ℝ)) (b := (-1 : ℝ)) (c := (1 : ℝ))
    negOneRegular negOneRegular oneRegular
    (by norm_num) (by norm_num) (by norm_num)

noncomputable def realDetTrace : IsFormallyRealDetTrace ℝ RealAlbert :=
  Octonion.detTrace
    (R := ℝ) (a := (-1 : ℝ)) (b := (-1 : ℝ)) (c := (1 : ℝ))
    negOneRegular negOneRegular oneRegular
    (by norm_num) (by norm_num) (by norm_num)

theorem real_rank_three : realDetTrace.rank = 3 := by
  rfl

noncomputable def realTraceUnit : TraceUnitData RealAlbert where
  unit := 1
  trace := realDetTrace.trace
  trace_unit := by
    calc
      realDetTrace.trace 1 = (realDetTrace.rank : ℝ) := realDetTrace.trace_one
      _ = 3 := by rw [real_rank_three]

/-- Bilinear Jordan multiplication bundled in the interface expected by DASHI. -/
noncomputable def realJordanMul : RealAlbert →ₗ[ℝ] RealAlbert →ₗ[ℝ] RealAlbert where
  toFun x :=
    { toFun := fun y => x * y
      map_add' := by intro y z; simp [mul_add]
      map_smul' := by intro r y; simp [mul_smul_comm] }
  map_add' := by
    intro x y
    ext z
    simp [add_mul]
  map_smul' := by
    intro r x
    ext y
    simp [smul_mul_assoc]

noncomputable def realAlbertStructure : AlbertStructure RealAlbert where
  traceUnit := realTraceUnit
  jordanMul := realJordanMul
  jordan_comm := by
    intro x y
    exact JordanAlgebra.jordan_mul_comm x y
  jordan_identity := by
    intro x y
    exact JordanAlgebra.jordan_identity x y
  unit_left := by
    intro x
    exact one_mul x
  cubic := realDetTrace.det
  cubic_unit := realDetTrace.det_one
  cubic_smul := by
    intro r x
    have h := realDetTrace.det_smul r x
    rw [real_rank_three] at h
    simpa [smul_eq_mul] using h

/-- If this file kernel-checks in the DASHI environment, the native generic
scalar/traceless theorem applies to the actual standard real Albert carrier. -/
noncomputable def realScalarTracelessEquiv :
    RealAlbert ≃ₗ[ℝ] ℝ × Traceless realTraceUnit :=
  scalarTracelessEquiv realTraceUnit

#check realAlbertStructure
#check realScalarTracelessEquiv

end ExternalAlbert.RealAlbertAdapterProbe
