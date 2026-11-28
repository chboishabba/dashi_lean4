import YangMills.WilsonCylinderCompactification

namespace RequestProject.YangMills

example
    {Ω : Type*}
    (raw : ℕ → Ω → ℝ) :
    CountableWilsonDF2Source (WilsonCylinderState raw) :=
  wilsonCylinderDF2Source raw

example
    {Ω : Type*}
    (raw : ℕ → Ω → ℝ) :
    Function.Injective
      (fun x : WilsonCylinderState raw =>
        fun i => wilsonCylinderCoordinate raw i x) :=
  wilsonCylinderCoordinateMap_injective raw

end RequestProject.YangMills
