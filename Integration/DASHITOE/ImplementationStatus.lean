namespace DASHITOE

def sourceWritten : Bool := true

def kernelVerified : Bool := false

def verificationBoundary : String :=
  "TOE implementation is source-written and source-reviewed. No Lean or Lake executable was available in the execution environment, so no exact-head kernel verification is claimed."

end DASHITOE
