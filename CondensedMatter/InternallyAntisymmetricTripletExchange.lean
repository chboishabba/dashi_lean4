import Mathlib

namespace CondensedMatter

/--
Exchange parity under swapping the two electrons in a Cooper pair.
Even is symmetric (+1), odd is antisymmetric (-1).
-/
inductive ExchangeParity
  | even
  | odd
  deriving DecidableEq, Repr

namespace ExchangeParity

def mul : ExchangeParity → ExchangeParity → ExchangeParity
  | .even, p => p
  | .odd, .even => .odd
  | .odd, .odd => .even

instance : Mul ExchangeParity := ⟨mul⟩

@[simp] theorem even_mul (p : ExchangeParity) : .even * p = p := rfl
@[simp] theorem odd_mul_even : .odd * .even = .odd := rfl
@[simp] theorem odd_mul_odd : .odd * .odd = .even := rfl

theorem mul_assoc (a b c : ExchangeParity) :
    (a * b) * c = a * (b * c) := by
  cases a <;> cases b <;> cases c <;> rfl

end ExchangeParity

/--
Exchange coordinates for a Cooper-pair state. Fermionic statistics require
the product of spatial, spin, and orbital exchange parities to be odd.
-/
structure PairExchangeSector where
  spatial : ExchangeParity
  spin : ExchangeParity
  orbital : ExchangeParity
  deriving Repr

def totalExchangeParity (P : PairExchangeSector) : ExchangeParity :=
  P.spatial * P.spin * P.orbital

def onsiteTripletOrbitalAntisymmetric : PairExchangeSector where
  spatial := .even
  spin := .even
  orbital := .odd

theorem int_pairing_is_fermionic :
    totalExchangeParity onsiteTripletOrbitalAntisymmetric = .odd := rfl

def onsiteTripletOrbitalSymmetric : PairExchangeSector where
  spatial := .even
  spin := .even
  orbital := .even

theorem orbital_antisymmetry_is_essential_in_this_sector :
    totalExchangeParity onsiteTripletOrbitalSymmetric = .even := rfl

end CondensedMatter
