import NobelChemistry.SourcePaidWeld

namespace NobelChemistry

example : soai2003Cycles = 3 := by rfl
example : soai2003Initial < soai2003Threshold := by
  norm_num [soai2003Initial, soai2003Threshold]
example : activationBarrierDeciKJ SoaiSystem.TMSPym = 859 := by rfl
example : reactionODECount + sideReactionODECount = totalODECount := by
  norm_num [reactionODECount, sideReactionODECount, totalODECount]
example : soai1996Initial < soai1996Terminal := by
  norm_num [soai1996Initial, soai1996Terminal]

end NobelChemistry
