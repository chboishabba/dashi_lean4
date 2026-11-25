import Synthesis.MonsterSignedEndpointComposition

/-!
# Original three central projection ranges

The Fourier identities are algebraic source obligations on the original
central operator, not a second 196884-dimensional carrier. This compiler
takes the actual three orthogonal complete projectors and constructs the
linear splitting; phase zero is its literal range. Unequal sector dimensions
are permitted. No recognition from dimensions or numerical probes.
-/
namespace Synthesis.MonsterCentralProjectorSplit
noncomputable section
universe u
variable {k W : Type u} [Field k] [AddCommGroup W] [Module k W]

structure Projectors where
  p : Fin 3 → W →ₗ[k] W
  orthogonal : ∀ i j w, p i (p j w) = if i = j then p i w else 0
  complete : ∀ w, p 0 w + (p 1 w + p 2 w) = w

variable (D : Projectors (k := k) (W := W))

abbrev Sector (i : Fin 3) := LinearMap.range (D.p i)

def component (i : Fin 3) (w : W) : Sector D i :=
  ⟨D.p i w, ⟨w,rfl⟩⟩

theorem onRange (i j : Fin 3) (w : Sector D j) :
    D.p i (w : W) = if i = j then (w : W) else 0 := by
  obtain ⟨v,hv⟩ := w.property
  by_cases h : i = j
  · subst j
    simpa [hv] using D.orthogonal i i v
  · simpa [hv,h] using D.orthogonal i j v

/-- Construct the full vector splitting from the original projection laws. -/
def split : W ≃ₗ[k] (Sector D 0 × (Sector D 1 × Sector D 2)) where
  toFun w := (component D 0 w, component D 1 w, component D 2 w)
  invFun x := (x.1 : W) + ((x.2.1 : W) + (x.2.2 : W))
  left_inv := D.complete
  right_inv := by
    intro x
    have h01 : (0 : Fin 3) ≠ 1 := by decide
    have h02 : (0 : Fin 3) ≠ 2 := by decide
    have h12 : (1 : Fin 3) ≠ 2 := by decide
    apply Prod.ext
    · apply Subtype.ext
      change D.p 0 ((x.1 : W) + ((x.2.1 : W) + (x.2.2 : W))) = (x.1 : W)
      simp [map_add, onRange, h01, h02]
    · apply Prod.ext
      · apply Subtype.ext
        change D.p 1 ((x.1 : W) + ((x.2.1 : W) + (x.2.2 : W))) = (x.2.1 : W)
        simp [map_add, onRange, Ne.symm h01, h12]
      · apply Subtype.ext
        change D.p 2 ((x.1 : W) + ((x.2.1 : W) + (x.2.2 : W))) = (x.2.2 : W)
        simp [map_add, onRange, Ne.symm h02, Ne.symm h12]
  map_add' := by
    intro x y
    apply Prod.ext
    · apply Subtype.ext
      exact (D.p 0).map_add x y
    · apply Prod.ext
      · apply Subtype.ext
        exact (D.p 1).map_add x y
      · apply Subtype.ext
        exact (D.p 2).map_add x y
  map_smul' := by
    intro c x
    apply Prod.ext
    · apply Subtype.ext
      exact (D.p 0).map_smul c x
    · apply Prod.ext
      · apply Subtype.ext
        exact (D.p 1).map_smul c x
      · apply Subtype.ext
        exact (D.p 2).map_smul c x

/-- Inverter sends each literal projection range to the marked target range.
The Fourier polynomial covariance supplies the commutation equation. -/
theorem arrowOnRanges (g : W →ₗ[k] W) (i j : Fin 3)
    (h : ∀ w, g (D.p i w) = D.p j (g w)) (x : Sector D i) :
    g (x : W) ∈ Sector D j := by
  obtain ⟨w,hw⟩ := x.property
  exact ⟨g w, (h w).symm.trans (congrArg g hw)⟩

end
end Synthesis.MonsterCentralProjectorSplit
