/-! Secondary mirror of DASHI.Interop.OpaqueRuntimeVersionBoundaryExact.
The hexadecimal-looking token has no proven ABI or execution semantics. -/
namespace AgdaMirror.OpaqueRuntimeVersionBoundary

structure OpaqueRuntimeToken where
  token : String
  version : Nat
  executableVerified : Bool

def unresolvedToken (version : Nat) : OpaqueRuntimeToken :=
  ⟨"0xffff1000", version, false⟩

def reviseVersion (next : Nat) (item : OpaqueRuntimeToken) :
    OpaqueRuntimeToken :=
  ⟨item.token, next, false⟩

theorem revisionPreservesToken (next : Nat) (item : OpaqueRuntimeToken) :
    (reviseVersion next item).token = item.token := rfl

theorem revisionDoesNotVerifyExecution (next : Nat) (item : OpaqueRuntimeToken) :
    (reviseVersion next item).executableVerified = false := rfl

theorem unresolvedIsNotVerified (version : Nat) :
    (unresolvedToken version).executableVerified = false := rfl

end AgdaMirror.OpaqueRuntimeVersionBoundary
