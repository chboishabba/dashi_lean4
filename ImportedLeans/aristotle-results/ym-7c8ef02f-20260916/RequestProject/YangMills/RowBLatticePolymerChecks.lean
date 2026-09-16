/-
# Axiom checks for the lattice polymer entropy lane

Records that the lattice-animal counting bound, the four-dimensional entropy
rate and the resulting shell-energy statements rest on no axioms beyond the
three standard ones, and that the animal predicate is inhabited.
-/
import RequestProject.YangMills.RowBLatticePolymerEnergy

namespace YangMills

section AxiomChecks

-- the combinatorial core
#print axioms exists_boundary_edge
#print axioms coverWalk_insert
#print axioms exists_coverWalk
#print axioms animals_ncard_le

-- the exponential entropy form and the four-dimensional lattice
#print axioms animals_entropy
#print axioms animal_shell_card_le
#print axioms latticeStep_involutive
#print axioms lattice4_animals_entropy

-- the Row-B shell energy with the entropy half discharged
#print axioms lattice4_marked_shell_energy_geometric
#print axioms lattice4_marked_shell_energy_tsum_le
#print axioms isAnimal_singleton

end AxiomChecks

end YangMills
