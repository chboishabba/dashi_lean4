import Mathlib

/-!
# Selected 3B action equality from a same-object three-eigenspace decomposition

For an order-three characteristic-zero action, equality of character data is
not enough to identify operators.  A sufficient same-object criterion is much
stronger and very concrete: the actual Monster restriction and the selected
producer must act with the same eigenvalues on the SAME three subspaces, and
those subspaces must span the carrier.

This theorem reduces the remaining 3B action weld to exactly that spectral
same-object statement.  It does not infer shared eigenspaces from dimensions
or the trace-53 fingerprint.
-/

namespace Integration.Selected3BActionEqualityFromSpectralDecomposition

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem linearMap_eq_of_same_three_eigenspaces
    (actual selected : V →ₗ[ℂ] V)
    (ζ : ℂ)
    (Eone Ezeta EzetaSq : Submodule ℂ V)
    (hspan :
      ∀ v : V, ∃ x : Eone, ∃ y : Ezeta, ∃ z : EzetaSq,
        (x : V) + (y : V) + (z : V) = v)
    (hActualOne : ∀ x : Eone, actual x = x)
    (hActualZeta : ∀ y : Ezeta, actual y = ζ • (y : V))
    (hActualZetaSq : ∀ z : EzetaSq, actual z = (ζ^2) • (z : V))
    (hSelectedOne : ∀ x : Eone, selected x = x)
    (hSelectedZeta : ∀ y : Ezeta, selected y = ζ • (y : V))
    (hSelectedZetaSq : ∀ z : EzetaSq, selected z = (ζ^2) • (z : V)) :
    actual = selected := by
  apply LinearMap.ext
  intro v
  obtain ⟨x, y, z, hv⟩ := hspan v
  rw [← hv]
  simp only [map_add]
  rw [hActualOne x, hActualZeta y, hActualZetaSq z,
      hSelectedOne x, hSelectedZeta y, hSelectedZetaSq z]

/-- A useful asymmetric form: once the selected producer is already known to
have the prescribed phase action on the common sectors, it is enough to prove
that the actual Monster action has those same restrictions. -/
theorem actual_eq_selected_of_common_phase_model
    (actual selected : V →ₗ[ℂ] V)
    (ζ : ℂ)
    (Eone Ezeta EzetaSq : Submodule ℂ V)
    (hspan :
      ∀ v : V, ∃ x : Eone, ∃ y : Ezeta, ∃ z : EzetaSq,
        (x : V) + (y : V) + (z : V) = v)
    (hSelectedOne : ∀ x : Eone, selected x = x)
    (hSelectedZeta : ∀ y : Ezeta, selected y = ζ • (y : V))
    (hSelectedZetaSq : ∀ z : EzetaSq, selected z = (ζ^2) • (z : V))
    (hActualOne : ∀ x : Eone, actual x = x)
    (hActualZeta : ∀ y : Ezeta, actual y = ζ • (y : V))
    (hActualZetaSq : ∀ z : EzetaSq, actual z = (ζ^2) • (z : V)) :
    actual = selected :=
  linearMap_eq_of_same_three_eigenspaces
    actual selected ζ Eone Ezeta EzetaSq hspan
    hActualOne hActualZeta hActualZetaSq
    hSelectedOne hSelectedZeta hSelectedZetaSq

end Integration.Selected3BActionEqualityFromSpectralDecomposition
