/-
# Certified finite carrier / exact reindex interface

The next multi-zero Schur stage should estimate the literal selected nuisance carrier,
not a parallel abstract matrix.  This file supplies the small exact reindex boundary:
a certified finite carrier may be reorganized by an explicit equivalence without
changing any finite aggregate.
-/
import Mathlib

namespace Zeta23Bridge
namespace CertifiedFiniteCarrierReindex

/-- A finite family whose indices are the actual certified carrier. -/
structure CertifiedFiniteCarrier where
  Index : Type
  instFintype : Fintype Index
  instDecidableEq : DecidableEq Index

attribute [instance] CertifiedFiniteCarrier.instFintype
attribute [instance] CertifiedFiniteCarrier.instDecidableEq

/-- An exact alternate ordering/coordinate system for the same carrier. -/
structure ExactReindex (c : CertifiedFiniteCarrier) where
  MajorIndex : Type
  instFintype : Fintype MajorIndex
  instDecidableEq : DecidableEq MajorIndex
  equiv : c.Index ≃ MajorIndex

attribute [instance] ExactReindex.instFintype
attribute [instance] ExactReindex.instDecidableEq

/-- Reindexing changes presentation only; it cannot manufacture or erase total weight. -/
theorem sum_reindex {c : CertifiedFiniteCarrier} (r : ExactReindex c)
    (f : c.Index → ℝ) :
    ∑ i, f i = ∑ j, f (r.equiv.symm j) := by
  exact (Equiv.sum_comp r.equiv.symm f).symm

/-- The same invariant for a two-coordinate literal response. -/
theorem sum_response_reindex {c : CertifiedFiniteCarrier} (r : ExactReindex c)
    (resp : c.Index → Fin 2 → ℝ) (j : Fin 2) :
    ∑ i, resp i j = ∑ k, resp (r.equiv.symm k) j := by
  exact sum_reindex r (fun i => resp i j)

end CertifiedFiniteCarrierReindex
end Zeta23Bridge
