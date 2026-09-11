import Synthesis.ToneCore
import Synthesis.DialecticTone
import Synthesis.RelationSeam
import Synthesis.MonsterFibre
import Synthesis.WalkGeometry
import Synthesis.MoonshineBase
import Synthesis.WalkArithmetic
import Synthesis.Vec15Fibre
import Synthesis.StatisticsFibre
import Synthesis.InferenceFibre
import Synthesis.PhysicsInterfaces
import Synthesis.SpinCoverBridge
import Synthesis.CircleCover
import Synthesis.ExponentFibre
import Synthesis.MonsterOrder
import Synthesis.MonsterCharacterDetermination
import Synthesis.MonsterCharacterMultiplicityRegression
import Synthesis.Hyperfabric
import Synthesis.CodecBridge
import Synthesis.EndToEnd
import Synthesis.AxiomAudit

/-!
# Cross-domain synthesis spine

Root module of the `Synthesis` library: a minimal, fully proved proof spine over
the cross-domain material in this repository.

Layers, in dependency order.

`Synthesis.MonsterCharacterDetermination` is the generic mathlib-backed
character donor.  `Synthesis.MonsterCharacterMultiplicityRegression` keeps the
new two-simple multiplicity API on the default build path; neither module makes
any Monster-specific same-object claim.
-/
