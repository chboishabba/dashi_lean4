import Integration.Paper9ExecutableCM163

/-!
Paper 9: original integer-typed finite Hecke gates, direct kernel admissions.

These are THE EXISTING original candidate arrays, exact signed
convolutions, and source finite integer certificates from
Paper9ExecutableCM163, not a new computation/model.

Unlike a Python acceptance receipt, `by decide` must reduce the
literal Lean Boolean definitions in the kernel; a FALSE flag or
resource exhaustion fails compilation. This is source-written and
has NOT been run by Lean. No native_decide, unsafe axiom, sorry,
opaque external CSV, arbitrary checked hypothesis, or CI invocation.

Each Boolean has its own declaration for checkpointed local runs;
for a 90s limit check unit first, then diagonal, then slice.
-/
namespace Integration.Paper9NativeOriginalFiniteGateAdmissions
open Integration.Paper9ExecutableCM163
open Integration.Paper9CM163LiteralPacket

set_option maxRecDepth 32768 in
theorem originalUnitOK : unitOK = true := by decide

set_option maxRecDepth 32768 in
theorem originalDiagonalOK : diagOK = true := by decide

set_option maxRecDepth 32768 in
theorem originalSliceOK : sliceOK = true := by decide

-- Reuse, without rewriting, the existing checker soundness welds.
theorem originalDiagonalCertificate : diagonalGate :=
  diagonalOfCheck originalUnitOK originalDiagonalOK

theorem originalSliceCertificate : sliceGate :=
  sliceOfCheck originalUnitOK originalSliceOK

-- This is purely the native finite source packet.
-- It is NOT global modular rigidity, a cusp analytic order factor,
-- an Agda source certificate, or the j=K CM root.
#print axioms originalDiagonalCertificate
#print axioms originalSliceCertificate
end Integration.Paper9NativeOriginalFiniteGateAdmissions
