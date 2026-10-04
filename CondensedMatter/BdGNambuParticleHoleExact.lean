import Mathlib

namespace CondensedMatter

/-!
Reusable algebraic BdG/Nambu particle-hole core.

DASHI contribution:
This file proves the block-level particle-hole identity for a BdG Hamiltonian
once the normal block and pairing block satisfy the standard transpose
relations. It does not assert that a particular material realizes those
relations; that identification belongs in a source/material adapter.
-/

variable {A : Type*} [AddGroup A]

structure BdGAlgebra where
  transpose : A → A
  conjugate : A → A
  transpose_involutive : ∀ a, transpose (transpose a) = a
  conjugate_involutive : ∀ a, conjugate (conjugate a) = a
  transpose_neg : ∀ a, transpose (-a) = -(transpose a)
  conjugate_neg : ∀ a, conjugate (-a) = -(conjugate a)

structure BdGBlock (A : Type*) where
  pp : A
  ph : A
  hp : A
  hh : A
  deriving Repr

namespace BdGBlock

variable (alg : BdGAlgebra (A := A))

def neg (H : BdGBlock A) : BdGBlock A :=
  ⟨-H.pp, -H.ph, -H.hp, -H.hh⟩

def particleHole (H : BdGBlock A) : BdGBlock A :=
  ⟨alg.conjugate H.hh,
   alg.conjugate H.hp,
   alg.conjugate H.ph,
   alg.conjugate H.pp⟩

end BdGBlock

def canonicalBdG
    (alg : BdGAlgebra (A := A))
    {K : Type*}
    (negK : K → K)
    (h Δ Δdag : K → A)
    (k : K) :
    BdGBlock A :=
  ⟨h k, Δ k, Δdag k, -(alg.transpose (h (negK k)))⟩

structure BdGPHSHypotheses
    (alg : BdGAlgebra (A := A))
    {K : Type*}
    (negK : K → K)
    (h Δ Δdag : K → A) : Prop where
  negK_involutive : ∀ k, negK (negK k) = k
  normal_conj_transpose :
    ∀ k, alg.conjugate (alg.transpose (h k)) = h k
  pairing_ph :
    ∀ k, alg.conjugate (Δdag k) = -(Δ (negK k))
  pairing_hp :
    ∀ k, alg.conjugate (Δ k) = -(Δdag (negK k))
  normal_particle :
    ∀ k, alg.conjugate (h k) = alg.transpose (h k)

theorem canonicalBdG_particleHole
    (alg : BdGAlgebra (A := A))
    {K : Type*}
    (negK : K → K)
    (h Δ Δdag : K → A)
    (hyp : BdGPHSHypotheses alg negK h Δ Δdag)
    (k : K) :
    BdGBlock.particleHole alg (canonicalBdG alg negK h Δ Δdag k)
      =
    BdGBlock.neg (canonicalBdG alg negK h Δ Δdag (negK k)) := by
  apply BdGBlock.ext <;>
    simp [BdGBlock.particleHole, BdGBlock.neg, canonicalBdG,
      hyp.pairing_ph, hyp.pairing_hp, hyp.normal_particle,
      hyp.negK_involutive, alg.conjugate_neg, hyp.normal_conj_transpose]

end CondensedMatter
