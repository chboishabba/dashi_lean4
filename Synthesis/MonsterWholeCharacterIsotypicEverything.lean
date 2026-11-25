import Synthesis.MonsterWholeCharacterModuleAdapter
import Synthesis.MonsterWholeCharacterSimpleSubobjectClassification
import Synthesis.MonsterWholeCharacterIsotypicAssembly
import Synthesis.MonsterWholeCharacterIsotypicAssemblyRegression
import Synthesis.MonsterTwoIsotypicBlockAssembly
import Synthesis.MonsterTwoIsotypicBlockAssemblyRegression

/-!
# Focused Monster whole-character / isotypic rollup

This rollup collects the generic representation-theory tail now available for
Monster 3B without importing Monster-specific same-object assumptions:

* FDRep <-> group-algebra action/submodule adapter;
* simple-source classification from a whole-character scalar multiple;
* one-type semisimple/isotypic finite-copy assembly;
* post-recognition copy-count cancellation;
* complementary two-isotypic-block assembly.

The remaining composition leaf is intentionally visible: turn each simple
`k[G]`-submodule of the SAME actual restricted Monster sector into the concrete
simple FDRep occurrence consumed by the whole-character classifier, preserving
the actual action.  No character label, dimension identity or source citation
is allowed to manufacture that same-object adapter.
-/
