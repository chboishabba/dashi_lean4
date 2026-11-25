import Synthesis.MonsterProjectedOriginalCharacter

/-!
# Original six-axis source observer and actual frame

Consumes the literal marked E words of the original
monster_3b_mmgroup_source_symplectic_basis.py producer, evaluated in the
original Monster representation. The sign convention is B_i A_j =
z^(delta_ij) A_j B_i. No second ambient carrier or independent vacuum
vector type is introduced.

The Fourier resolution and translation commutation identities on the
original group action are explicit inputs to the frame constructor;
their mathematical derivation from the source Weyl relations is recorded
in Monster3BLiteralWeylSourceAttachment20261125.md. Source-written only.
-/
namespace Synthesis.MonsterLiteralWeylFrame
noncomputable section
open Synthesis.MonsterWeightFrame
open Synthesis.MonsterProjectedOriginalCharacter
universe u
abbrev X6 := Fin 6 → Fin 3
abbrev ObserverIndex := Fin 3 × X6
variable {k G W : Type u} [Field k] [CharZero k] [Group G]
variable [AddCommGroup W] [Module k W] [FiniteDimensional k W]

/-- The same ordered literal words used by the original E producer.
Do not replace them with coordinate permutations on a synthetic carrier. -/
def axisWord (A : Fin 6 → G) (x : X6) : G :=
  (List.ofFn (fun i : Fin 6 => A i ^ (x i).val)).prod

def observerWord (z : G) (B : Fin 6 → G) (t : ObserverIndex) : G :=
  z ^ t.1.val * axisWord B t.2

/-- zeta is the selected phase scalar, not a signless exponent. -/
def observerCoefficient (zeta : k) (t : ObserverIndex) : k :=
  (2187 : k)⁻¹ * zeta ^ (2 * t.1.val)

/-- Literal ambient joint central/vacuum projector, before choosing bases. -/
def originalObserver (rho : Representation k G W) (z : G)
    (B : Fin 6 → G) (zeta : k) : Module.End k W :=
  wordObserver rho (observerCoefficient zeta) (observerWord z B)

theorem originalObserverTrace (rho : Representation k G W) (z : G)
    (B : Fin 6 → G) (zeta : k) (g : G) :
    LinearMap.trace k W ((originalObserver rho z B zeta).comp (rho g)) =
      ∑ t : ObserverIndex, observerCoefficient zeta t *
        LinearMap.trace k W (rho (observerWord z B t * g)) :=
  wordObserverTrace rho _ _ g

section FrameFromOriginalAction
variable {V : Type u} [AddCommGroup V] [Module k V]
variable (T : X6 → V ≃ₗ[k] V) (P : Module.End k V)
variable (idem : ∀ v, P (P v) = P v)

/-- The vacuum is the literal range of the actual projection. -/
abbrev Vacuum := LinearMap.range P

def translatedProjection (x : X6) : Module.End k V := (T x).conj P

def includeActual (x : X6) : Vacuum P →ₗ[k] V :=
  (T x).toLinearMap.comp (LinearMap.range P).subtype

def recoverActual (x : X6) : V →ₗ[k] Vacuum P where
  toFun v := ⟨P ((T x).symm v), ⟨(T x).symm v, rfl⟩⟩
  map_add' := by
    intro v w
    apply Subtype.ext
    change P ((T x).symm (v+w)) =
      P ((T x).symm v) + P ((T x).symm w)
    rw [map_add, map_add]
  map_smul' := by
    intro c v
    apply Subtype.ext
    change P ((T x).symm (c • v)) = c • P ((T x).symm v)
    rw [map_smul, map_smul]

theorem includeRecover (x : X6) (v : V) :
    includeActual T P x (recoverActual T P x v) =
      translatedProjection T P x v := rfl

theorem translatedIdempotent (x : X6) (v : V) :
    translatedProjection T P x (translatedProjection T P x v) =
      translatedProjection T P x v := by
  change T x (P ((T x).symm (T x (P ((T x).symm v))))) =
    T x (P ((T x).symm v))
  rw [LinearEquiv.symm_apply_apply, idem]

/-- Construct the existing Frame on the original range, using only
orthogonality and resolution of the translated original projector.
These are consequences of the literal six-axis Weyl commutators. -/
def literalFrame
    (orth : ∀ x y v, translatedProjection T P x
        (translatedProjection T P y v) =
          if x = y then translatedProjection T P y v else 0)
    (complete : ∀ v, (∑ x, translatedProjection T P x v) = v) :
    Frame (k := k) (S := Vacuum P) (W := V) (ι := X6) where
  includeWeight := includeActual T P
  recoverWeight := recoverActual T P
  orthogonal := by
    intro x y u
    have hu : P (u : V) = (u : V) := by
      obtain ⟨v,hv⟩ := u.property
      rw [← hv, idem]
    apply Subtype.ext
    by_cases h : x = y
    · subst y
      simp only [if_pos rfl]
      change P ((T x).symm (T x (u : V))) = (u : V)
      rw [LinearEquiv.symm_apply_apply, hu]
    · simp only [if_neg h]
      change P ((T x).symm (T y (u : V))) = 0
      apply (T x).injective
      have hh := orth x y (T y (u : V))
      change T x (P ((T x).symm
        (T y (P ((T y).symm (T y (u : V))))))) =
          if x = y then T y (P ((T y).symm (T y (u : V)))) else 0 at hh
      simp only [LinearEquiv.symm_apply_apply, hu, if_neg h] at hh
      simpa only [map_zero] using hh
  complete := by
    intro v
    simpa only [includeRecover] using complete v

end FrameFromOriginalAction
end
end Synthesis.MonsterLiteralWeylFrame
