import NobelChemistry.SourcePaidWeld

namespace NobelChemistry

example : soai2003Cycles = 3 := by rfl
example : soai2003Initial < soai2003Threshold := by norm_num [soai2003Initial, soai2003Threshold]
example : activationBarrierDeciKJ TMSPym = 859 := by rfl
example : reactionODECount + sideReactionODECount = totalODECount := by norm_num [reactionODECount, sideReactionODECount, totalODECount]

end NobelChemistry
