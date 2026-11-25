import Synthesis.MonsterActualParityCharacter

/-!
# Literal involution eigenspaces and half-projector BIDI

The central element is an actual group element of the given representation.
Construct its two literal eigenspaces, restrict the same action, and derive
the ParitySplit consumed by MonsterActualParityCharacter. No independent
block action or parity rank is assumed.
-/
namespace Synthesis.MonsterParityProjectors
noncomputable section
universe u
variable {k G V : Type u} [Field k] [CharZero k] [Group G]
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]
variable (rho : Representation k G V) (j : G)
variable (hj : j * j = 1) (hc : ∀ g : G, j * g = g * j)

def sector (s : k) : Submodule k V where
  carrier := {v | rho j v = s • v}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change rho j (x+y) = s • (x+y)
    rw [map_add, hx, hy, smul_add]
  smul_mem' := by
    intro a v hv
    change rho j (a • v) = s • (a • v)
    rw [map_smul, hv, smul_comm]

theorem square (v : V) : rho j (rho j v) = v := by
  have h := congrArg (fun g : G => rho g v) hj
  simpa only [map_mul, Module.End.mul_apply, map_one, Module.End.one_apply] using h

theorem commute (g : G) (v : V) : rho j (rho g v) = rho g (rho j v) := by
  have h := congrArg (fun a : G => rho a v) (hc g)
  simpa only [map_mul, Module.End.mul_apply] using h

def restricted (s : k) : Representation k G (sector rho j s) where
  toFun g :=
    { toFun := fun x => ⟨rho g x, by
        change rho j (rho g (x : V)) = s • rho g (x : V)
        rw [commute rho j hc, x.property, map_smul]⟩
      map_add' := by intro x y; apply Subtype.ext; exact (rho g).map_add _ _
      map_smul' := by intro a x; apply Subtype.ext; exact (rho g).map_smul _ _ }
  map_one' := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change rho 1 (x : V) = x
    simp
  map_mul' g h := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change rho (g*h) (x : V) = rho g (rho h (x : V))
    simp only [map_mul, Module.End.mul_apply]

def negPart (v : V) : sector rho j (-1) :=
  ⟨(2 : k)⁻¹ • (v - rho j v), by
    change rho j ((2 : k)⁻¹ • (v - rho j v)) =
      (-1 : k) • ((2 : k)⁻¹ • (v - rho j v))
    rw [map_smul, map_sub, square rho j hj]
    module⟩

def posPart (v : V) : sector rho j 1 :=
  ⟨(2 : k)⁻¹ • (v + rho j v), by
    change rho j ((2 : k)⁻¹ • (v + rho j v)) =
      (1 : k) • ((2 : k)⁻¹ • (v + rho j v))
    rw [map_smul, map_add, square rho j hj]
    module⟩

def split : V ≃ₗ[k] (sector rho j (-1) × sector rho j 1) where
  toFun v := (negPart rho j hj v, posPart rho j hj v)
  invFun x := (x.1 : V) + (x.2 : V)
  left_inv := by
    intro v
    change (2 : k)⁻¹ • (v-rho j v) + (2 : k)⁻¹ • (v+rho j v) = v
    module
  right_inv := by
    intro x
    have hn : rho j (x.1 : V) = -(x.1 : V) := by
      simpa using x.1.property
    have hp : rho j (x.2 : V) = (x.2 : V) := by
      simpa using x.2.property
    apply Prod.ext
    · apply Subtype.ext
      change (2 : k)⁻¹ • ((x.1 : V)+(x.2 : V)-
        rho j ((x.1 : V)+(x.2 : V))) = (x.1 : V)
      rw [map_add, hn, hp]
      module
    · apply Subtype.ext
      change (2 : k)⁻¹ • ((x.1 : V)+(x.2 : V)+
        rho j ((x.1 : V)+(x.2 : V))) = (x.2 : V)
      rw [map_add, hn, hp]
      module
  map_add' := by
    intro x y
    apply Prod.ext
    · apply Subtype.ext
      change (2 : k)⁻¹ • (x+y-rho j (x+y)) =
        (2 : k)⁻¹ • (x-rho j x)+(2 : k)⁻¹ • (y-rho j y)
      rw [map_add]
      module
    · apply Subtype.ext
      change (2 : k)⁻¹ • (x+y+rho j (x+y)) =
        (2 : k)⁻¹ • (x+rho j x)+(2 : k)⁻¹ • (y+rho j y)
      rw [map_add]
      module
  map_smul' := by
    intro a x
    apply Prod.ext
    · apply Subtype.ext
      change (2 : k)⁻¹ • (a • x-rho j (a • x)) =
        a • ((2 : k)⁻¹ • (x-rho j x))
      rw [map_smul]
      module
    · apply Subtype.ext
      change (2 : k)⁻¹ • (a • x+rho j (a • x)) =
        a • ((2 : k)⁻¹ • (x+rho j x))
      rw [map_smul]
      module

/-- All fields are derived on the same representation and literal ranges. -/
def actualParitySplit : Synthesis.MonsterActualParityCharacter.ParitySplit rho
    (restricted rho j hc (-1)) (restricted rho j hc 1) where
  split := split rho j hj
  j := j
  action := by
    intro g
    apply LinearMap.ext
    intro x
    change (split rho j hj) (rho g ((x.1 : V)+(x.2 : V))) =
      LinearMap.prodMap (restricted rho j hc (-1) g) (restricted rho j hc 1 g) x
    apply (split rho j hj).symm.injective
    rw [LinearEquiv.symm_apply_apply]
    change rho g ((x.1 : V)+(x.2 : V)) = rho g (x.1 : V) + rho g (x.2 : V)
    exact (rho g).map_add _ _
  negative := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change rho j (x : V) = -(x : V)
    simpa using x.property
  positive := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change rho j (x : V) = (x : V)
    simpa using x.property

end
end Synthesis.MonsterParityProjectors
