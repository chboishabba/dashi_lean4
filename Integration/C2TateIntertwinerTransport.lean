import Mathlib

/-!
# C2 Tate transport under an intertwining additive equivalence

For an involutive additive action g on an abelian group M define

  N_g(x) = x + g x
  D_g(x) = g x - x.

Ordinary C2 Tate cohomology is represented by

  Hhat0 = Fix(g) / im(N_g)
  Hhat1 = ker(N_g) / im(D_g).

If an additive equivalence phi : M ~=+ N intertwines actions

  phi (g x) = h (phi x),

then phi transports fixed points, norm images, norm kernels and difference
images bijectively.  This is the exact generic theorem needed for the
2B-pure Klein-four lane: a Monster-local element conjugating one selected
2B involution to another gives same-shaped Tate data once its action on the
underlying integral Moonshine module is supplied.

No Monster-specific transport map is fabricated here.
-/

namespace Integration.C2TateIntertwinerTransport

variable {M N : Type*}
  [AddCommGroup M] [AddCommGroup N]

def c2Norm (g : M →+ M) (x : M) : M := x + g x
def c2Diff (g : M →+ M) (x : M) : M := g x - x

def Fixed (g : M →+ M) (x : M) : Prop := g x = x
def NormImage (g : M →+ M) (x : M) : Prop :=
  ∃ y, c2Norm g y = x
def NormKernel (g : M →+ M) (x : M) : Prop :=
  c2Norm g x = 0
def DiffImage (g : M →+ M) (x : M) : Prop :=
  ∃ y, c2Diff g y = x

variable
  (g : M →+ M) (h : N →+ N)
  (φ : M ≃+ N)
  (hIntertwine : ∀ x, φ (g x) = h (φ x))

theorem norm_intertwines (x : M) :
    φ (c2Norm g x) = c2Norm h (φ x) := by
  simp [c2Norm, hIntertwine]

theorem diff_intertwines (x : M) :
    φ (c2Diff g x) = c2Diff h (φ x) := by
  simp [c2Diff, hIntertwine]

theorem fixed_iff (x : M) :
    Fixed g x ↔ Fixed h (φ x) := by
  constructor
  · intro hx
    dsimp [Fixed] at hx ⊢
    rw [← hIntertwine, hx]
  · intro hx
    dsimp [Fixed] at hx ⊢
    apply φ.injective
    rw [hIntertwine]
    exact hx

theorem normImage_iff (x : M) :
    NormImage g x ↔ NormImage h (φ x) := by
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨φ y, ?_⟩
    rw [← norm_intertwines g h φ hIntertwine, hy]
  · rintro ⟨z, hz⟩
    refine ⟨φ.symm z, ?_⟩
    apply φ.injective
    rw [norm_intertwines g h φ hIntertwine]
    simpa using hz

theorem normKernel_iff (x : M) :
    NormKernel g x ↔ NormKernel h (φ x) := by
  constructor
  · intro hx
    dsimp [NormKernel] at hx ⊢
    rw [← norm_intertwines g h φ hIntertwine, hx]
    exact map_zero φ
  · intro hx
    dsimp [NormKernel] at hx ⊢
    apply φ.injective
    rw [norm_intertwines g h φ hIntertwine]
    simpa using hx

theorem diffImage_iff (x : M) :
    DiffImage g x ↔ DiffImage h (φ x) := by
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨φ y, ?_⟩
    rw [← diff_intertwines g h φ hIntertwine, hy]
  · rintro ⟨z, hz⟩
    refine ⟨φ.symm z, ?_⟩
    apply φ.injective
    rw [diff_intertwines g h φ hIntertwine]
    simpa using hz

theorem hhat0_representative_transport (x : M) :
    (Fixed g x ∧ ¬ NormImage g x)
      ↔
    (Fixed h (φ x) ∧ ¬ NormImage h (φ x)) := by
  rw [fixed_iff g h φ hIntertwine,
      normImage_iff g h φ hIntertwine]

theorem hhat1_representative_transport (x : M) :
    (NormKernel g x ∧ ¬ DiffImage g x)
      ↔
    (NormKernel h (φ x) ∧ ¬ DiffImage h (φ x)) := by
  rw [normKernel_iff g h φ hIntertwine,
      diffImage_iff g h φ hIntertwine]

theorem target_involutive_of_source
    (hg : ∀ x, g (g x) = x) :
    ∀ y, h (h y) = y := by
  intro y
  obtain ⟨x, rfl⟩ := φ.surjective y
  apply φ.injective
  rw [← hIntertwine, ← hIntertwine, hg]

end Integration.C2TateIntertwinerTransport
