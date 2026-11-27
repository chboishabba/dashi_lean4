/-! Secondary mirror of DASHI.Interop.FileUrlRequestBoundaryExact.
No network retrieval, checksum verification or authority promotion. -/
namespace AgdaMirror.FileUrlRequestBoundary

structure FileUrlRequest where
  fileLabel : String
  sourceUrl : String
  requestedAction : String

structure PendingFileRequest where
  request : FileUrlRequest
  fetched : Bool
  checksumVerified : Bool
  authorityAccepted : Bool

def prepareFileRequest (req : FileUrlRequest) : PendingFileRequest :=
  ⟨req, false, false, false⟩

theorem requestPreserved (req : FileUrlRequest) :
    (prepareFileRequest req).request = req := rfl

theorem notFetched (req : FileUrlRequest) :
    (prepareFileRequest req).fetched = false := rfl

theorem checksumNotVerified (req : FileUrlRequest) :
    (prepareFileRequest req).checksumVerified = false := rfl

theorem authorityNotAccepted (req : FileUrlRequest) :
    (prepareFileRequest req).authorityAccepted = false := rfl

end AgdaMirror.FileUrlRequestBoundary
