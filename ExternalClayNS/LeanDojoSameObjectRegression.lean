import LeanDojoExactTerminal

/-!
Regression surface for the literal same-object Navier--Stokes external weld.

This file deliberately contains no proof construction.  It requires the
representation maps and final exact LeanDojo theorem terms to remain available.
-/

namespace DASHILiteralClayNS

#check pairToLeanSpacetime
#check leanSpacetimeToPair
#check pairToLeanSpacetime_leftInverse
#check pairToLeanSpacetime_rightInverse
#check comparatorInitialDecay_to_leanDojo
#check comparatorInitialPeriodic_to_leanDojo
#check comparatorForceDecay_to_leanDojo
#check comparatorPeriodicForceDecay_to_leanDojo
#check leanDojoR3Solution_to_comparator
#check leanDojoPeriodicSolution_to_comparator
#check dashiExactFeffermanC
#check dashiExactFeffermanD

#print axioms dashiExactFeffermanC
#print axioms dashiExactFeffermanD

end DASHILiteralClayNS
