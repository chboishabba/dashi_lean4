import Mathlib
import YangMills.CMP119RegularComponentPolymerDictionary

namespace RequestProject.YangMills

example
    {L : ℕ}
    (dict : CMP119RegularComponentPolymerDictionary L)
    (links : SU2TorusLinks L) :
    dict.sourceRegular links =
      ∑ c in dict.components, dict.evaluate c links :=
  dict.source_regular_eq_component_sum links

end RequestProject.YangMills
