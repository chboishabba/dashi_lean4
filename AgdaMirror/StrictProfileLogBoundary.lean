/-! Secondary mirror of DASHI.Interop.StrictProfileLogBoundaryExact.
Strict configuration is not an executed runtime receipt. -/
namespace AgdaMirror.StrictProfileLogBoundary

structure StrictLogProfile where
  profileName : String
  version : Nat
  strictRequested : Bool

structure LogEntry where
  profile : StrictLogProfile
  message : String
  runtimeVerified : Bool

def appendStrictLog (name : String) (version : Nat) (message : String) :
    LogEntry :=
  ⟨⟨name, version, true⟩, message, false⟩

theorem appendRequestsStrict (name : String) (version : Nat) (message : String) :
    (appendStrictLog name version message).profile.strictRequested = true := rfl

theorem appendPreservesVersion (name : String) (version : Nat) (message : String) :
    (appendStrictLog name version message).profile.version = version := rfl

theorem appendDoesNotAttestRuntime (name : String) (version : Nat)
    (message : String) :
    (appendStrictLog name version message).runtimeVerified = false := rfl

end AgdaMirror.StrictProfileLogBoundary
