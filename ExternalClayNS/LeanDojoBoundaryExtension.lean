import Mathlib

/-!
# Closed-time boundary extension used by the LeanDojo same-object weld

LeanDojo stores its Navier--Stokes equations on `t > 0` and smoothness on
`t >= 0`.  The comparator/frozen Clay target writes the corresponding sliced
equations on `t >= 0`.  This file pays the generic topology step once: two
continuous functions agreeing for every positive time agree on the entire
closed half-line.
-/

namespace DASHILiteralClayNS

open Set

/-- Equality on positive time extends to the closed nonnegative half-line for
continuous target-valued functions. -/
theorem eqOn_Ici_zero_of_eqOn_Ioi_zero
    {E : Type*} [TopologicalSpace E] [T2Space E]
    {f g : ℝ → E}
    (hf : ContinuousOn f (Ici 0))
    (hg : ContinuousOn g (Ici 0))
    (hpos : Set.EqOn f g (Ioi 0)) :
    Set.EqOn f g (Ici 0) := by
  apply hpos.of_subset_closure hf hg
  · intro t ht
    exact le_of_lt ht
  · intro t ht
    rw [closure_Ioi]
    exact ht

/-- Pointwise version used at a selected nonnegative time. -/
theorem eq_of_pos_eq_of_continuousOn_Ici
    {E : Type*} [TopologicalSpace E] [T2Space E]
    {f g : ℝ → E}
    (hf : ContinuousOn f (Ici 0))
    (hg : ContinuousOn g (Ici 0))
    (hpos : ∀ t, 0 < t → f t = g t)
    {t : ℝ} (ht : 0 ≤ t) :
    f t = g t := by
  exact eqOn_Ici_zero_of_eqOn_Ioi_zero hf hg
    (fun s hs => hpos s hs) ht

/-- In particular, only the time-zero value is new when the open-time equation
is already available. -/
theorem eq_zero_of_pos_eq_of_continuousOn_Ici
    {E : Type*} [TopologicalSpace E] [T2Space E]
    {f g : ℝ → E}
    (hf : ContinuousOn f (Ici 0))
    (hg : ContinuousOn g (Ici 0))
    (hpos : ∀ t, 0 < t → f t = g t) :
    f 0 = g 0 :=
  eq_of_pos_eq_of_continuousOn_Ici hf hg hpos (by exact le_rfl)

end DASHILiteralClayNS
