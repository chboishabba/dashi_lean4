import Mathlib
import AgdaMirror.Ultrametric

/-!
# Lean mirror of `Contraction.agda` (definitional scaffolding, faithful)

Faithful transcription of `Contraction.agda`: strict contraction properties of a
map `K` with respect to an ultrametric, both the everywhere version
(`Contractive`) and the non-degenerate version on distinct points
(`ContractiveNe`), plus the `StrictContraction` bundle that also names a unique
fixed point.
-/

namespace AgdaMirror

/-- Strict contraction everywhere (note: over a `ℕ`-valued distance this is in
fact unsatisfiable, since it forces `d (K x) (K x) < d x x = 0`; we transcribe it
faithfully nonetheless, matching the Agda record). -/
structure Contractive {S : Type} (U : Ultrametric S) (K : S → S) where
  contraction : ∀ x y, U.d (K x) (K y) < U.d x y

/-- Strict contraction on distinct points (avoids the degenerate `x = x` case). -/
structure ContractiveNe {S : Type} (U : Ultrametric S) (K : S → S) where
  contractionNe : ∀ {x y}, x ≠ y → U.d (K x) (K y) < U.d x y

/-- Strict contraction plus a specified unique fixed point. -/
structure StrictContraction {S : Type} (U : Ultrametric S) (K : S → S) where
  contractiveNe : ContractiveNe U K
  fp : S
  fixed : K fp = fp
  unique : ∀ x, K x = x → x = fp

end AgdaMirror
