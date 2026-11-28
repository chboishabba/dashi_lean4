import Mathlib
import Welds.PNPF3SyndromeBoundaryExact
import Welds.PNPIntrinsicPatchExact

namespace PNPTargetTrellis
open PNPF3SyndromeBoundary

-- At an actual prefix cut, the remaining target is in the suffix
-- image V, and the used syndrome is in the prefix image U.
def Residual {r : Nat} (U V : Submodule (ZMod 3) (Syndrome r))
    (t : Syndrome r) := {y : Syndrome r // y ∈ V ∧ t-y ∈ U}

-- The exact affine translate of the intersection, not the ambient rank.
noncomputable def crossingEquiv {r : Nat}
    (U V : Submodule (ZMod 3) (Syndrome r)) (t : Syndrome r)
    (y₀ : Residual U V t) :
    Residual U V t ≃ ↥(V ⊓ U) where
  toFun y := ⟨y.val-y₀.val, by
    have h := (boundary_translate V U t y₀.val (y.val-y₀.val) y₀.property)
    have e : y₀.val+(y.val-y₀.val)=y.val := by abel
    exact h.mp (by rw [e]; exact y.property)⟩
  invFun d := ⟨y₀.val+d.val,
    (boundary_translate V U t y₀.val d.val y₀.property).mpr d.property⟩
  left_inv y := by ext; abel
  right_inv d := by ext; abel

-- If a source continuation exists, suffix-image rejection is impossible.
-- This is a NECESSARY linear filter; Boolean/clause restrictions remain.
theorem cannot_drop_lift {r : Nat} (U V : Submodule (ZMod 3) (Syndrome r))
    (used rest t : Syndrome r) (hu : used ∈ U) (hv : rest ∈ V)
    (h : used+rest=t) : t-used ∈ V ∧ t-(t-used) ∈ U := by
  have e : t-used=rest := by rw [← h]; abel
  constructor
  · rwa [e]
  · have e' : t-(t-used)=used := by abel
    rwa [e']

-- Original prefix class: residual syndrome and the set of not-yet-hit
-- clauses determine suffix admissibility, not the representative prefix.
def advance {r : Nat} (a : Syndrome r) (hit : Finset Nat)
    (p : Syndrome r × Finset Nat) (b : Bool) :
    Syndrome r × Finset Nat :=
  (p.1-(if b then a else 0),p.2 \ hit)

theorem merge_exact {r : Nat} (a : Syndrome r) (hit : Finset Nat)
    (p q : Syndrome r × Finset Nat) (h : p=q) (b : Bool) :
    advance a hit p b=advance a hit q b := congrArg (fun x => advance a hit x b) h

theorem residual_step {r : Nat} (used a t : Syndrome r) (b : Bool) :
    t-(used+(if b then a else 0))=(t-used)-(if b then a else 0) := by abel

-- State merging must add all original lifts, not count one per label.
theorem mass_preserved (a b c d : Nat) :
    (a+b)+(c+d)=(a+c)+(b+d) := by omega

-- At a fixed cut, all clauses wholly before the cut have already
-- been satisfied; untouched clauses have fixed unresolved status.
-- Only crossing clauses carry variable bits. This injection is the
-- exact finite state-count receiver once those bits are extracted.
theorem state_capacity {X : Type*} [Fintype X] {r w : Nat}
    (U V : Submodule (ZMod 3) (Syndrome r)) (t : Syndrome r)
    (y₀ : Residual U V t) (syndrome : X → Residual U V t)
    (live : X → Fin w → Bool)
    (inj : Function.Injective (fun x => (syndrome x,live x))) :
    Fintype.card X ≤ Fintype.card ↥(V ⊓ U) * 2^w := by
  classical
  let f := fun x : X => (crossingEquiv U V t y₀ (syndrome x),live x)
  have hf : Function.Injective f := by
    intro x y h
    apply inj
    exact Prod.ext ((crossingEquiv U V t y₀).injective (congrArg Prod.fst h))
      (congrArg Prod.snd h)
  simpa using Fintype.card_le_of_injective f hf

end PNPTargetTrellis
