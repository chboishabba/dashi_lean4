/-! Secondary mirror of DASHI.Interop.FP16SupportBoundaryExact.
Reported support is not independently probed device capability. -/
namespace AgdaMirror.FP16SupportBoundary

inductive FP16Decision where
  | denied
  | permittedByReceipt
  deriving DecidableEq

structure FP16SupportRequest where
  requested : Bool
  reportedSupported : Bool

def decideFP16 : FP16SupportRequest → FP16Decision
  | ⟨true, true⟩ => .permittedByReceipt
  | _ => .denied

theorem unsupportedDenied :
    decideFP16 ⟨true, false⟩ = .denied := rfl

theorem notRequestedDenied (supported : Bool) :
    decideFP16 ⟨false, supported⟩ = .denied := by
  cases supported <;> rfl

theorem receiptAllowsOnlyRequested :
    decideFP16 ⟨true, true⟩ = .permittedByReceipt := rfl

end AgdaMirror.FP16SupportBoundary
