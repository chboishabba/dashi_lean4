import Integration.DASHITOE.ConcreteInhabitants

namespace DASHITOE

example (x : AtomicP2Basis) : atomicP2C3 (atomicP2C3 (atomicP2C3 x)) = x :=
  atomicP2C3_order_three x

example (a b : AtomicP2Basis) :
    atomicP2CoulombMatrix (atomicP2C3 a) (atomicP2C3 b) =
      atomicP2CoulombMatrix a b :=
  atomicP2Coulomb_c3_invariant a b

example : eisensteinOmega ^ 3 = (1 : EisensteinField) := eisensteinOmega_cube

example : lean68RTInhabitant.authority = .importedFormalInhabitant := rfl
example : lean68JacobsonInhabitant.authority = .importedFormalInhabitant := rfl
example : lean73CMInhabitant.authority = .importedFormalInhabitant := rfl

end DASHITOE
