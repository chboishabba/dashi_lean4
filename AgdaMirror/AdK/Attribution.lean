import Mathlib
import AgdaMirror.AuthorityBoundary

/-!
# AdK attribution coordinates

This file carries source/provenance coordinates only.  It does not turn a DOI,
PDB identifier, repository revision, or executable result into scientific or
theorem authority.

Attribution split:

* **Li–Liu–Ji 2015** (DOI `10.1016/j.bpj.2015.06.059`) owns the source-facing
  AdK CV residue/domain roles used in this mirror.
* **Prohaska et al.** (DOI `10.1515/pac-2019-0603`) owns the adopted abridged
  atomic-weight convention used by the exact rational reconstruction.
* **wwPDB/PDB** owns deposition/object identity; entry identity does not choose
  a chain/model/altloc policy or manufacture coordinate equality.
* **JMD / meta-introspector** owns the Agda↔Lean interoperability/provenance
  machinery integrated into the `dashi_lean4` base at commit
  `349f9b7dd49a7f23bfbd7d9da60416afa5440ccf`.
* **DASHI** owns the exact rational reconstruction and the bridge mathematics
  proved under `AgdaMirror.AdK`.
-/

namespace AgdaMirror.AdK.Attribution

structure SourceCoordinate where
  owner : String
  identifier : String
  role : String
  deriving DecidableEq, Repr

def liLiuJi2015 : SourceCoordinate :=
  { owner := "Li-Liu-Ji 2015"
    identifier := "doi:10.1016/j.bpj.2015.06.059"
    role := "source-facing AdK CV residue/domain roles" }

def prohaskaAtomicWeights : SourceCoordinate :=
  { owner := "Prohaska et al."
    identifier := "doi:10.1515/pac-2019-0603"
    role := "adopted abridged atomic-weight convention" }

def pdb4AKE : SourceCoordinate :=
  { owner := "wwPDB/PDB"
    identifier := "doi:10.2210/pdb4AKE/pdb"
    role := "open structural-reference object identity" }

def pdb1AKE : SourceCoordinate :=
  { owner := "wwPDB/PDB"
    identifier := "doi:10.2210/pdb1AKE/pdb"
    role := "closed structural-reference object identity" }

def jmdInteropBase : SourceCoordinate :=
  { owner := "JMD / meta-introspector"
    identifier := "dashi_lean4:349f9b7dd49a7f23bfbd7d9da60416afa5440ccf"
    role := "Agda↔Lean interoperability and provenance machinery" }

def dashiReconstruction : SourceCoordinate :=
  { owner := "DASHI"
    identifier := "AgdaMirror.AdK"
    role := "exact rational reconstruction and bridge theorems" }

/-- The mirror explicitly refuses the inference `source identifier → theorem authority`. -/
def sourceIdentifierCreatesTheoremAuthority : Bool := false

/-- JMD interoperability machinery is retained as provenance/infrastructure, not
as the scientific owner of the AdK CV definitions. -/
def jmdInteropCreatesAdKScientificAuthority : Bool := false

example : sourceIdentifierCreatesTheoremAuthority = false := rfl
example : jmdInteropCreatesAdKScientificAuthority = false := rfl

end AgdaMirror.AdK.Attribution
