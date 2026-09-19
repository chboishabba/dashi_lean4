import AgdaMirror.AdK.PDBMirrorSelectedFixture
import AgdaMirror.AdK.CanonicalSelectionContent
import AgdaMirror.AdK.SourceSelections

/-!
# AdK mirror-selected fixture validation

This validation requires transparent exact-rational selected-coordinate fixtures
for the observed GitHub transport mirrors.  It deliberately validates the
selected manifestation, not canonical wwPDB byte parity and not source authority.
-/

namespace AgdaMirror.AdK.PDBMirrorSelectedFixtureValidation

open AgdaMirror.AdK.PDBMirrorSelectedFixture
open AgdaMirror.AdK.SourceSelections
open AgdaMirror.AdK.CanonicalSelectionContent

#check fourAKEChainA
#check oneAKEChainA
#check fourAKEChainB
#check oneAKEChainB
#check fourAKEChainA.configuration
#check oneAKEChainA.configuration

example : fourAKEChainA.canonicalArchiveByteEqualityObserved = false := rfl
example : oneAKEChainA.canonicalArchiveByteEqualityObserved = false := rfl
example : fourAKEChainA.scientificAuthorityPromotedFromMirror = false := rfl
example : oneAKEChainA.scientificAuthorityPromotedFromMirror = false := rfl
example : fourAKEChainB.canonicalArchiveByteEqualityObserved = false := rfl
example : oneAKEChainB.scientificAuthorityPromotedFromMirror = false := rfl

#check canonicalContent fourAKEChainA.configuration theta1Lid
#check canonicalContent oneAKEChainA.configuration theta1Lid
#check canonicalContent fourAKEChainA.configuration (dlnLid .heavy)
#check canonicalContent oneAKEChainA.configuration (dlnNmp .heavy)
#check canonicalContent fourAKEChainB.configuration theta1Lid
#check canonicalContent oneAKEChainB.configuration (dlnNmp .heavy)

end AgdaMirror.AdK.PDBMirrorSelectedFixtureValidation
