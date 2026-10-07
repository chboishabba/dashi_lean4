import Mathlib
import YangMills.ProjectiveCylinderPhysicalReflectionWeld

open MeasureTheory

namespace RequestProject.YangMills

example
    {Ω Test : Type*} [MeasurableSpace Ω]
    (weld : PhysicalCylinderReflectionWeld Ω Test) :
    RealCountableObservableNormMomentSource.ProjectiveCylinderOSPositive
      weld.source weld.cylinderReflectedProduct :=
  physical_cylinder_os_positive weld

end RequestProject.YangMills
