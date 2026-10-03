import Mathlib.Tactic
import NSBControl.Rational345RealSnapshotSparse
import NSBControl.Rational345Round71RealityField
import NSBControl.Rational345Round71TransverseField

/-!
# Physicality of the rational 3-4-5 initial state

The R830 initial state has only six nonzero modes: three canonical positive
representatives and their conjugate negatives.  This file closes the two
initial conditions needed by the Round853 live-packet lane on the full radius-
four carrier: Fourier reality and divergence freedom.
-/

namespace NSBControl
namespace Rational345Round71InitialPhysical

open Rational345RealRadius4
open Rational345RealInitialState
open Rational345RealSnapshotSparse
open Rational345Round71PhysicalCarrier
open Rational345Round71RealityField
open Rational345Round71TransverseField

@[simp] theorem negate_k300 : negateMode k300 = km300 := by native_decide
@[simp] theorem negate_km300 : negateMode km300 = k300 := by native_decide
@[simp] theorem negate_k040 : negateMode k040 = k0m40 := by native_decide
@[simp] theorem negate_k0m40 : negateMode k0m40 = k040 := by native_decide
@[simp] theorem negate_k340 : negateMode k340 = km3m40 := by native_decide
@[simp] theorem negate_km3m40 : negateMode km3m40 = k340 := by native_decide

/-- The six-mode seed support is closed under Fourier negation. -/
theorem seedModes_negate_mem_iff (k : Mode) :
    negateMode k ∈ seedModes ↔ k ∈ seedModes := by
  constructor
  · intro h
    simp [seedModes] at h ⊢
    rcases h with h | h | h | h | h | h
    · have := congrArg negateMode h
      simp at this
      aesop
    · have := congrArg negateMode h
      simp at this
      aesop
    · have := congrArg negateMode h
      simp at this
      aesop
    · have := congrArg negateMode h
      simp at this
      aesop
    · have := congrArg negateMode h
      simp at this
      aesop
    · have := congrArg negateMode h
      simp at this
      aesop
  · intro h
    simp [seedModes] at h ⊢
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

/-- The concrete initial state is fixed by the global Fourier reality
involution. -/
theorem initial_reality : realityTransform u₀ = u₀ := by
  funext k
  by_cases hk : k ∈ seedModes
  · simp [seedModes] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [realityTransform, u₀, vecConj]
  · have hneg : negateMode k ∉ seedModes := by
      intro h
      exact hk ((seedModes_negate_mem_iff k).mp h)
    rw [realityTransform_apply,
        u₀_zero_of_not_mem_seed hneg,
        u₀_zero_of_not_mem_seed hk]
    simp [vecConj]

/-- Transversality is preserved when a positive seed is reflected to its
conjugate negative mode. -/
theorem transverse_negate_conj
    {k : Mode} {v : Vec3}
    (h : bilinearDot (kComplex k) v = 0) :
    bilinearDot (kComplex (negateMode k)) (vecConj v) = 0 := by
  rw [bilinearDot_mode_neg_conj, h]
  simp

/-- Every radius-four Fourier slot of the initial state is divergence-free. -/
theorem initial_transverse (k : Mode) :
    bilinearDot (kComplex k) (u₀ k) = 0 := by
  by_cases hk : k ∈ seedModes
  · simp [seedModes] at hk
    rcases hk with h | h | h | h | h | h
    · subst k
      rw [u₀_km3m40, ← negate_k340]
      exact transverse_negate_conj transverse_v340
    · subst k
      rw [u₀_km300, ← negate_k300]
      exact transverse_negate_conj transverse_v300
    · subst k
      rw [u₀_k0m40, ← negate_k040]
      exact transverse_negate_conj transverse_v040
    · subst k
      simpa [u₀_k040] using transverse_v040
    · subst k
      simpa [u₀_k300] using transverse_v300
    · subst k
      simpa [u₀_k340] using transverse_v340
  · rw [u₀_zero_of_not_mem_seed hk]
    simp [bilinearDot]

/-- The selected initial datum satisfies both physical linear constraints. -/
def initialPhysicalClosed : Bool := true

end Rational345Round71InitialPhysical
end NSBControl
