/-
# Fiber sums of the primes with a single power in range (`p = 17, …, 71`)

For each of these fourteen primes only `p` itself lies in the displayed range, so the fiber sum
consists of the single term `τ(p)/p^{11/2}`.  Each value is pinned down to six decimal places.
-/
import RequestProject.FiberSumsMulti

namespace FiberSums

open PrimeFibers RamanujanTau

/-! ### The fiber of `17`: the powers 17 -/

private theorem approx_17 : |normTau 17 - (-1.179650499416)| ≤ 1e-9 :=
  normTau_approx (n := 17) (t := -6905934) (by native_decide) (a := 5854220.384272614655)
    (b := 5854220.384272614656) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem absApprox_17 : |(|normTau 17| - 1.179650499416)| ≤ 1e-9 := by
  have h := abs_approx_of_approx approx_17
  rwa [show |((-1.179650499416) : ℝ)| = 1.179650499416 from by norm_num] at h

/-- The fiber sum of `17`, written out over its 1 power. -/
theorem signedFiberSum_17_eq : signedFiberSum 17 256 = normTau 17 := by
  rw [signedFiberSum, sum_primePowerFiber _ (by norm_num) (by norm_num),
    show Nat.log 17 256 = 1 from by decide]
  norm_num [Finset.sum_Icc_succ_top]

/-- The absolute fiber sum of `17`, written out over its 1 power. -/
theorem absFiberSum_17_eq : absFiberSum 17 256 = |normTau 17| := by
  rw [absFiberSum, sum_primePowerFiber _ (by norm_num) (by norm_num),
    show Nat.log 17 256 = 1 from by decide]
  norm_num [Finset.sum_Icc_succ_top]

/-- The signed fiber sum of `17` is `-1.179650`, to six decimal places. -/
theorem signedFiberSum_17 : |signedFiberSum 17 256 - (-1.179650)| ≤ 1e-6 := by
  have he := signedFiberSum_17_eq
  have h17 := approx_17
  rw [he]
  simp only [abs_le] at *
  constructor <;> norm_num <;> linarith [h17.1, h17.2]

/-- The absolute fiber sum of `17` is `1.179650`, to six decimal places. -/
theorem absFiberSum_17 : |absFiberSum 17 256 - 1.179650| ≤ 1e-6 := by
  have he := absFiberSum_17_eq
  have h17 := absApprox_17
  rw [he]
  simp only [abs_le] at *
  constructor <;> norm_num <;> linarith [h17.1, h17.2]

/-! ### The fiber of `19`: the powers 19 -/

private theorem approx_19 : |normTau 19 - 0.987802787127| ≤ 1e-9 :=
  normTau_approx (n := 19) (t := 10661420) (by native_decide) (a := 10793065.315202118242)
    (b := 10793065.315202118243) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem absApprox_19 : |(|normTau 19| - 0.987802787127)| ≤ 1e-9 := by
  have h := abs_approx_of_approx approx_19
  rwa [show |(0.987802787127 : ℝ)| = 0.987802787127 from by norm_num] at h

/-- The fiber sum of `19`, written out over its 1 power. -/
theorem signedFiberSum_19_eq : signedFiberSum 19 256 = normTau 19 := by
  rw [signedFiberSum, sum_primePowerFiber _ (by norm_num) (by norm_num),
    show Nat.log 19 256 = 1 from by decide]
  norm_num [Finset.sum_Icc_succ_top]

/-- The absolute fiber sum of `19`, written out over its 1 power. -/
theorem absFiberSum_19_eq : absFiberSum 19 256 = |normTau 19| := by
  rw [absFiberSum, sum_primePowerFiber _ (by norm_num) (by norm_num),
    show Nat.log 19 256 = 1 from by decide]
  norm_num [Finset.sum_Icc_succ_top]

/-- The signed fiber sum of `19` is `0.987803`, to six decimal places. -/
theorem signedFiberSum_19 : |signedFiberSum 19 256 - 0.987803| ≤ 1e-6 := by
  have he := signedFiberSum_19_eq
  have h19 := approx_19
  rw [he]
  simp only [abs_le] at *
  constructor <;> norm_num <;> linarith [h19.1, h19.2]

/-- The absolute fiber sum of `19` is `0.987803`, to six decimal places. -/
theorem absFiberSum_19 : |absFiberSum 19 256 - 0.987803| ≤ 1e-6 := by
  have he := absFiberSum_19_eq
  have h19 := absApprox_19
  rw [he]
  simp only [abs_le] at *
  constructor <;> norm_num <;> linarith [h19.1, h19.2]

/-! ### The fiber of `23`: the powers 23 -/

private theorem approx_23 : |normTau 23 - 0.603975104681| ≤ 1e-9 :=
  normTau_approx (n := 23) (t := 18643272) (by native_decide) (a := 30867616.654253159232)
    (b := 30867616.654253159233) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem absApprox_23 : |(|normTau 23| - 0.603975104681)| ≤ 1e-9 := by
  have h := abs_approx_of_approx approx_23
  rwa [show |(0.603975104681 : ℝ)| = 0.603975104681 from by norm_num] at h

/-- The fiber sum of `23`, written out over its 1 power. -/
theorem signedFiberSum_23_eq : signedFiberSum 23 256 = normTau 23 := by
  rw [signedFiberSum, sum_primePowerFiber _ (by norm_num) (by norm_num),
    show Nat.log 23 256 = 1 from by decide]
  norm_num [Finset.sum_Icc_succ_top]

/-- The absolute fiber sum of `23`, written out over its 1 power. -/
theorem absFiberSum_23_eq : absFiberSum 23 256 = |normTau 23| := by
  rw [absFiberSum, sum_primePowerFiber _ (by norm_num) (by norm_num),
    show Nat.log 23 256 = 1 from by decide]
  norm_num [Finset.sum_Icc_succ_top]

/-- The signed fiber sum of `23` is `0.603975`, to six decimal places. -/
theorem signedFiberSum_23 : |signedFiberSum 23 256 - 0.603975| ≤ 1e-6 := by
  have he := signedFiberSum_23_eq
  have h23 := approx_23
  rw [he]
  simp only [abs_le] at *
  constructor <;> norm_num <;> linarith [h23.1, h23.2]

/-- The absolute fiber sum of `23` is `0.603975`, to six decimal places. -/
theorem absFiberSum_23 : |absFiberSum 23 256 - 0.603975| ≤ 1e-6 := by
  have he := absFiberSum_23_eq
  have h23 := absApprox_23
  rw [he]
  simp only [abs_le] at *
  constructor <;> norm_num <;> linarith [h23.1, h23.2]

/-! ### The fiber of `29`: the powers 29 -/

private theorem approx_29 : |normTau 29 - 1.162514717339| ≤ 1e-9 :=
  normTau_approx (n := 29) (t := 128406630) (by native_decide) (a := 110455917.748692075226)
    (b := 110455917.748692075227) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem absApprox_29 : |(|normTau 29| - 1.162514717339)| ≤ 1e-9 := by
  have h := abs_approx_of_approx approx_29
  rwa [show |(1.162514717339 : ℝ)| = 1.162514717339 from by norm_num] at h

/-- The fiber sum of `29`, written out over its 1 power. -/
theorem signedFiberSum_29_eq : signedFiberSum 29 256 = normTau 29 := by
  rw [signedFiberSum, sum_primePowerFiber _ (by norm_num) (by norm_num),
    show Nat.log 29 256 = 1 from by decide]
  norm_num [Finset.sum_Icc_succ_top]

/-- The absolute fiber sum of `29`, written out over its 1 power. -/
theorem absFiberSum_29_eq : absFiberSum 29 256 = |normTau 29| := by
  rw [absFiberSum, sum_primePowerFiber _ (by norm_num) (by norm_num),
    show Nat.log 29 256 = 1 from by decide]
  norm_num [Finset.sum_Icc_succ_top]

/-- The signed fiber sum of `29` is `1.162515`, to six decimal places. -/
theorem signedFiberSum_29 : |signedFiberSum 29 256 - 1.162515| ≤ 1e-6 := by
  have he := signedFiberSum_29_eq
  have h29 := approx_29
  rw [he]
  simp only [abs_le] at *
  constructor <;> norm_num <;> linarith [h29.1, h29.2]

/-- The absolute fiber sum of `29` is `1.162515`, to six decimal places. -/
theorem absFiberSum_29 : |absFiberSum 29 256 - 1.162515| ≤ 1e-6 := by
  have he := absFiberSum_29_eq
  have h29 := absApprox_29
  rw [he]
  simp only [abs_le] at *
  constructor <;> norm_num <;> linarith [h29.1, h29.2]

/-! ### The fiber of `31`: the powers 31 -/

private theorem approx_31 : |normTau 31 - (-0.331512211057)| ≤ 1e-9 :=
  normTau_approx (n := 31) (t := -52843168) (by native_decide) (a := 159400366.675879484941)
    (b := 159400366.675879484942) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem absApprox_31 : |(|normTau 31| - 0.331512211057)| ≤ 1e-9 := by
  have h := abs_approx_of_approx approx_31
  rwa [show |((-0.331512211057) : ℝ)| = 0.331512211057 from by norm_num] at h

/-- The fiber sum of `31`, written out over its 1 power. -/
theorem signedFiberSum_31_eq : signedFiberSum 31 256 = normTau 31 := by
  rw [signedFiberSum, sum_primePowerFiber _ (by norm_num) (by norm_num),
    show Nat.log 31 256 = 1 from by decide]
  norm_num [Finset.sum_Icc_succ_top]

/-- The absolute fiber sum of `31`, written out over its 1 power. -/
theorem absFiberSum_31_eq : absFiberSum 31 256 = |normTau 31| := by
  rw [absFiberSum, sum_primePowerFiber _ (by norm_num) (by norm_num),
    show Nat.log 31 256 = 1 from by decide]
  norm_num [Finset.sum_Icc_succ_top]

/-- The signed fiber sum of `31` is `-0.331512`, to six decimal places. -/
theorem signedFiberSum_31 : |signedFiberSum 31 256 - (-0.331512)| ≤ 1e-6 := by
  have he := signedFiberSum_31_eq
  have h31 := approx_31
  rw [he]
  simp only [abs_le] at *
  constructor <;> norm_num <;> linarith [h31.1, h31.2]

/-- The absolute fiber sum of `31` is `0.331512`, to six decimal places. -/
theorem absFiberSum_31 : |absFiberSum 31 256 - 0.331512| ≤ 1e-6 := by
  have he := absFiberSum_31_eq
  have h31 := absApprox_31
  rw [he]
  simp only [abs_le] at *
  constructor <;> norm_num <;> linarith [h31.1, h31.2]

/-! ### The fiber of `37`: the powers 37 -/

private theorem approx_37 : |normTau 37 - (-0.431986947257)| ≤ 1e-9 :=
  normTau_approx (n := 37) (t := -182213314) (by native_decide) (a := 421802823.342210943290)
    (b := 421802823.342210943291) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem absApprox_37 : |(|normTau 37| - 0.431986947257)| ≤ 1e-9 := by
  have h := abs_approx_of_approx approx_37
  rwa [show |((-0.431986947257) : ℝ)| = 0.431986947257 from by norm_num] at h

/-- The fiber sum of `37`, written out over its 1 power. -/
theorem signedFiberSum_37_eq : signedFiberSum 37 256 = normTau 37 := by
  rw [signedFiberSum, sum_primePowerFiber _ (by norm_num) (by norm_num),
    show Nat.log 37 256 = 1 from by decide]
  norm_num [Finset.sum_Icc_succ_top]

/-- The absolute fiber sum of `37`, written out over its 1 power. -/
theorem absFiberSum_37_eq : absFiberSum 37 256 = |normTau 37| := by
  rw [absFiberSum, sum_primePowerFiber _ (by norm_num) (by norm_num),
    show Nat.log 37 256 = 1 from by decide]
  norm_num [Finset.sum_Icc_succ_top]

/-- The signed fiber sum of `37` is `-0.431987`, to six decimal places. -/
theorem signedFiberSum_37 : |signedFiberSum 37 256 - (-0.431987)| ≤ 1e-6 := by
  have he := signedFiberSum_37_eq
  have h37 := approx_37
  rw [he]
  simp only [abs_le] at *
  constructor <;> norm_num <;> linarith [h37.1, h37.2]

/-- The absolute fiber sum of `37` is `0.431987`, to six decimal places. -/
theorem absFiberSum_37 : |absFiberSum 37 256 - 0.431987| ≤ 1e-6 := by
  have he := absFiberSum_37_eq
  have h37 := absApprox_37
  rw [he]
  simp only [abs_le] at *
  constructor <;> norm_num <;> linarith [h37.1, h37.2]

/-! ### The fiber of `41`: the powers 41 -/

private theorem approx_41 : |normTau 41 - 0.415345299834| ≤ 1e-9 :=
  normTau_approx (n := 41) (t := 308120442) (by native_decide) (a := 741841648.679991841424)
    (b := 741841648.679991841425) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem absApprox_41 : |(|normTau 41| - 0.415345299834)| ≤ 1e-9 := by
  have h := abs_approx_of_approx approx_41
  rwa [show |(0.415345299834 : ℝ)| = 0.415345299834 from by norm_num] at h

/-- The fiber sum of `41`, written out over its 1 power. -/
theorem signedFiberSum_41_eq : signedFiberSum 41 256 = normTau 41 := by
  rw [signedFiberSum, sum_primePowerFiber _ (by norm_num) (by norm_num),
    show Nat.log 41 256 = 1 from by decide]
  norm_num [Finset.sum_Icc_succ_top]

/-- The absolute fiber sum of `41`, written out over its 1 power. -/
theorem absFiberSum_41_eq : absFiberSum 41 256 = |normTau 41| := by
  rw [absFiberSum, sum_primePowerFiber _ (by norm_num) (by norm_num),
    show Nat.log 41 256 = 1 from by decide]
  norm_num [Finset.sum_Icc_succ_top]

/-- The signed fiber sum of `41` is `0.415345`, to six decimal places. -/
theorem signedFiberSum_41 : |signedFiberSum 41 256 - 0.415345| ≤ 1e-6 := by
  have he := signedFiberSum_41_eq
  have h41 := approx_41
  rw [he]
  simp only [abs_le] at *
  constructor <;> norm_num <;> linarith [h41.1, h41.2]

/-- The absolute fiber sum of `41` is `0.415345`, to six decimal places. -/
theorem absFiberSum_41 : |absFiberSum 41 256 - 0.415345| ≤ 1e-6 := by
  have he := absFiberSum_41_eq
  have h41 := absApprox_41
  rw [he]
  simp only [abs_le] at *
  constructor <;> norm_num <;> linarith [h41.1, h41.2]

/-! ### The fiber of `43`: the powers 43 -/

private theorem approx_43 : |normTau 43 - (-0.017765278869)| ≤ 1e-9 :=
  normTau_approx (n := 43) (t := -17125708) (by native_decide) (a := 963998827.525854777686)
    (b := 963998827.525854777687) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem absApprox_43 : |(|normTau 43| - 0.017765278869)| ≤ 1e-9 := by
  have h := abs_approx_of_approx approx_43
  rwa [show |((-0.017765278869) : ℝ)| = 0.017765278869 from by norm_num] at h

/-- The fiber sum of `43`, written out over its 1 power. -/
theorem signedFiberSum_43_eq : signedFiberSum 43 256 = normTau 43 := by
  rw [signedFiberSum, sum_primePowerFiber _ (by norm_num) (by norm_num),
    show Nat.log 43 256 = 1 from by decide]
  norm_num [Finset.sum_Icc_succ_top]

/-- The absolute fiber sum of `43`, written out over its 1 power. -/
theorem absFiberSum_43_eq : absFiberSum 43 256 = |normTau 43| := by
  rw [absFiberSum, sum_primePowerFiber _ (by norm_num) (by norm_num),
    show Nat.log 43 256 = 1 from by decide]
  norm_num [Finset.sum_Icc_succ_top]

/-- The signed fiber sum of `43` is `-0.017765`, to six decimal places. -/
theorem signedFiberSum_43 : |signedFiberSum 43 256 - (-0.017765)| ≤ 1e-6 := by
  have he := signedFiberSum_43_eq
  have h43 := approx_43
  rw [he]
  simp only [abs_le] at *
  constructor <;> norm_num <;> linarith [h43.1, h43.2]

/-- The absolute fiber sum of `43` is `0.017765`, to six decimal places. -/
theorem absFiberSum_43 : |absFiberSum 43 256 - 0.017765| ≤ 1e-6 := by
  have he := absFiberSum_43_eq
  have h43 := absApprox_43
  rw [he]
  simp only [abs_le] at *
  constructor <;> norm_num <;> linarith [h43.1, h43.2]

/-! ### The fiber of `47`: the powers 47 -/

private theorem approx_47 : |normTau 47 - 1.709172005305| ≤ 1e-9 :=
  normTau_approx (n := 47) (t := 2687348496) (by native_decide) (a := 1572310152.318559667640)
    (b := 1572310152.318559667641) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem absApprox_47 : |(|normTau 47| - 1.709172005305)| ≤ 1e-9 := by
  have h := abs_approx_of_approx approx_47
  rwa [show |(1.709172005305 : ℝ)| = 1.709172005305 from by norm_num] at h

/-- The fiber sum of `47`, written out over its 1 power. -/
theorem signedFiberSum_47_eq : signedFiberSum 47 256 = normTau 47 := by
  rw [signedFiberSum, sum_primePowerFiber _ (by norm_num) (by norm_num),
    show Nat.log 47 256 = 1 from by decide]
  norm_num [Finset.sum_Icc_succ_top]

/-- The absolute fiber sum of `47`, written out over its 1 power. -/
theorem absFiberSum_47_eq : absFiberSum 47 256 = |normTau 47| := by
  rw [absFiberSum, sum_primePowerFiber _ (by norm_num) (by norm_num),
    show Nat.log 47 256 = 1 from by decide]
  norm_num [Finset.sum_Icc_succ_top]

/-- The signed fiber sum of `47` is `1.709172`, to six decimal places. -/
theorem signedFiberSum_47 : |signedFiberSum 47 256 - 1.709172| ≤ 1e-6 := by
  have he := signedFiberSum_47_eq
  have h47 := approx_47
  rw [he]
  simp only [abs_le] at *
  constructor <;> norm_num <;> linarith [h47.1, h47.2]

/-- The absolute fiber sum of `47` is `1.709172`, to six decimal places. -/
theorem absFiberSum_47 : |absFiberSum 47 256 - 1.709172| ≤ 1e-6 := by
  have he := absFiberSum_47_eq
  have h47 := absApprox_47
  rw [he]
  simp only [abs_le] at *
  constructor <;> norm_num <;> linarith [h47.1, h47.2]

/-! ### The fiber of `53`: the powers 53 -/

private theorem approx_53 : |normTau 53 - (-0.524240730569)| ≤ 1e-9 :=
  normTau_approx (n := 53) (t := -1596055698) (by native_decide) (a := 3044509144.241841753677)
    (b := 3044509144.241841753678) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem absApprox_53 : |(|normTau 53| - 0.524240730569)| ≤ 1e-9 := by
  have h := abs_approx_of_approx approx_53
  rwa [show |((-0.524240730569) : ℝ)| = 0.524240730569 from by norm_num] at h

/-- The fiber sum of `53`, written out over its 1 power. -/
theorem signedFiberSum_53_eq : signedFiberSum 53 256 = normTau 53 := by
  rw [signedFiberSum, sum_primePowerFiber _ (by norm_num) (by norm_num),
    show Nat.log 53 256 = 1 from by decide]
  norm_num [Finset.sum_Icc_succ_top]

/-- The absolute fiber sum of `53`, written out over its 1 power. -/
theorem absFiberSum_53_eq : absFiberSum 53 256 = |normTau 53| := by
  rw [absFiberSum, sum_primePowerFiber _ (by norm_num) (by norm_num),
    show Nat.log 53 256 = 1 from by decide]
  norm_num [Finset.sum_Icc_succ_top]

/-- The signed fiber sum of `53` is `-0.524241`, to six decimal places. -/
theorem signedFiberSum_53 : |signedFiberSum 53 256 - (-0.524241)| ≤ 1e-6 := by
  have he := signedFiberSum_53_eq
  have h53 := approx_53
  rw [he]
  simp only [abs_le] at *
  constructor <;> norm_num <;> linarith [h53.1, h53.2]

/-- The absolute fiber sum of `53` is `0.524241`, to six decimal places. -/
theorem absFiberSum_53 : |absFiberSum 53 256 - 0.524241| ≤ 1e-6 := by
  have he := absFiberSum_53_eq
  have h53 := absApprox_53
  rw [he]
  simp only [abs_le] at *
  constructor <;> norm_num <;> linarith [h53.1, h53.2]

/-! ### The fiber of `59`: the powers 59 -/

private theorem approx_59 : |normTau 59 - (-0.944962683061)| ≤ 1e-9 :=
  normTau_approx (n := 59) (t := -5189203740) (by native_decide) (a := 5491437739.311795444167)
    (b := 5491437739.311795444168) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem absApprox_59 : |(|normTau 59| - 0.944962683061)| ≤ 1e-9 := by
  have h := abs_approx_of_approx approx_59
  rwa [show |((-0.944962683061) : ℝ)| = 0.944962683061 from by norm_num] at h

/-- The fiber sum of `59`, written out over its 1 power. -/
theorem signedFiberSum_59_eq : signedFiberSum 59 256 = normTau 59 := by
  rw [signedFiberSum, sum_primePowerFiber _ (by norm_num) (by norm_num),
    show Nat.log 59 256 = 1 from by decide]
  norm_num [Finset.sum_Icc_succ_top]

/-- The absolute fiber sum of `59`, written out over its 1 power. -/
theorem absFiberSum_59_eq : absFiberSum 59 256 = |normTau 59| := by
  rw [absFiberSum, sum_primePowerFiber _ (by norm_num) (by norm_num),
    show Nat.log 59 256 = 1 from by decide]
  norm_num [Finset.sum_Icc_succ_top]

/-- The signed fiber sum of `59` is `-0.944963`, to six decimal places. -/
theorem signedFiberSum_59 : |signedFiberSum 59 256 - (-0.944963)| ≤ 1e-6 := by
  have he := signedFiberSum_59_eq
  have h59 := approx_59
  rw [he]
  simp only [abs_le] at *
  constructor <;> norm_num <;> linarith [h59.1, h59.2]

/-- The absolute fiber sum of `59` is `0.944963`, to six decimal places. -/
theorem absFiberSum_59 : |absFiberSum 59 256 - 0.944963| ≤ 1e-6 := by
  have he := absFiberSum_59_eq
  have h59 := absApprox_59
  rw [he]
  simp only [abs_le] at *
  constructor <;> norm_num <;> linarith [h59.1, h59.2]

/-! ### The fiber of `61`: the powers 61 -/

private theorem approx_61 : |normTau 61 - 1.054569884035| ≤ 1e-9 :=
  normTau_approx (n := 61) (t := 6956478662) (by native_decide) (a := 6596507986.157209122567)
    (b := 6596507986.157209122568) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem absApprox_61 : |(|normTau 61| - 1.054569884035)| ≤ 1e-9 := by
  have h := abs_approx_of_approx approx_61
  rwa [show |(1.054569884035 : ℝ)| = 1.054569884035 from by norm_num] at h

/-- The fiber sum of `61`, written out over its 1 power. -/
theorem signedFiberSum_61_eq : signedFiberSum 61 256 = normTau 61 := by
  rw [signedFiberSum, sum_primePowerFiber _ (by norm_num) (by norm_num),
    show Nat.log 61 256 = 1 from by decide]
  norm_num [Finset.sum_Icc_succ_top]

/-- The absolute fiber sum of `61`, written out over its 1 power. -/
theorem absFiberSum_61_eq : absFiberSum 61 256 = |normTau 61| := by
  rw [absFiberSum, sum_primePowerFiber _ (by norm_num) (by norm_num),
    show Nat.log 61 256 = 1 from by decide]
  norm_num [Finset.sum_Icc_succ_top]

/-- The signed fiber sum of `61` is `1.054570`, to six decimal places. -/
theorem signedFiberSum_61 : |signedFiberSum 61 256 - 1.054570| ≤ 1e-6 := by
  have he := signedFiberSum_61_eq
  have h61 := approx_61
  rw [he]
  simp only [abs_le] at *
  constructor <;> norm_num <;> linarith [h61.1, h61.2]

/-- The absolute fiber sum of `61` is `1.054570`, to six decimal places. -/
theorem absFiberSum_61 : |absFiberSum 61 256 - 1.054570| ≤ 1e-6 := by
  have he := absFiberSum_61_eq
  have h61 := absApprox_61
  rw [he]
  simp only [abs_le] at *
  constructor <;> norm_num <;> linarith [h61.1, h61.2]

/-! ### The fiber of `67`: the powers 67 -/

private theorem approx_67 : |normTau 67 - (-1.400911795679)| ≤ 1e-9 :=
  normTau_approx (n := 67) (t := -15481826884) (by native_decide) (a := 11051250286.957038106035)
    (b := 11051250286.957038106036) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem absApprox_67 : |(|normTau 67| - 1.400911795679)| ≤ 1e-9 := by
  have h := abs_approx_of_approx approx_67
  rwa [show |((-1.400911795679) : ℝ)| = 1.400911795679 from by norm_num] at h

/-- The fiber sum of `67`, written out over its 1 power. -/
theorem signedFiberSum_67_eq : signedFiberSum 67 256 = normTau 67 := by
  rw [signedFiberSum, sum_primePowerFiber _ (by norm_num) (by norm_num),
    show Nat.log 67 256 = 1 from by decide]
  norm_num [Finset.sum_Icc_succ_top]

/-- The absolute fiber sum of `67`, written out over its 1 power. -/
theorem absFiberSum_67_eq : absFiberSum 67 256 = |normTau 67| := by
  rw [absFiberSum, sum_primePowerFiber _ (by norm_num) (by norm_num),
    show Nat.log 67 256 = 1 from by decide]
  norm_num [Finset.sum_Icc_succ_top]

/-- The signed fiber sum of `67` is `-1.400912`, to six decimal places. -/
theorem signedFiberSum_67 : |signedFiberSum 67 256 - (-1.400912)| ≤ 1e-6 := by
  have he := signedFiberSum_67_eq
  have h67 := approx_67
  rw [he]
  simp only [abs_le] at *
  constructor <;> norm_num <;> linarith [h67.1, h67.2]

/-- The absolute fiber sum of `67` is `1.400912`, to six decimal places. -/
theorem absFiberSum_67 : |absFiberSum 67 256 - 1.400912| ≤ 1e-6 := by
  have he := absFiberSum_67_eq
  have h67 := absApprox_67
  rw [he]
  simp only [abs_le] at *
  constructor <;> norm_num <;> linarith [h67.1, h67.2]

/-! ### The fiber of `71`: the powers 71 -/

private theorem approx_71 : |normTau 71 - 0.644061971436| ≤ 1e-9 :=
  normTau_approx (n := 71) (t := 9791485272) (by native_decide) (a := 15202706736.686778740692)
    (b := 15202706736.686778740693) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem absApprox_71 : |(|normTau 71| - 0.644061971436)| ≤ 1e-9 := by
  have h := abs_approx_of_approx approx_71
  rwa [show |(0.644061971436 : ℝ)| = 0.644061971436 from by norm_num] at h

/-- The fiber sum of `71`, written out over its 1 power. -/
theorem signedFiberSum_71_eq : signedFiberSum 71 256 = normTau 71 := by
  rw [signedFiberSum, sum_primePowerFiber _ (by norm_num) (by norm_num),
    show Nat.log 71 256 = 1 from by decide]
  norm_num [Finset.sum_Icc_succ_top]

/-- The absolute fiber sum of `71`, written out over its 1 power. -/
theorem absFiberSum_71_eq : absFiberSum 71 256 = |normTau 71| := by
  rw [absFiberSum, sum_primePowerFiber _ (by norm_num) (by norm_num),
    show Nat.log 71 256 = 1 from by decide]
  norm_num [Finset.sum_Icc_succ_top]

/-- The signed fiber sum of `71` is `0.644062`, to six decimal places. -/
theorem signedFiberSum_71 : |signedFiberSum 71 256 - 0.644062| ≤ 1e-6 := by
  have he := signedFiberSum_71_eq
  have h71 := approx_71
  rw [he]
  simp only [abs_le] at *
  constructor <;> norm_num <;> linarith [h71.1, h71.2]

/-- The absolute fiber sum of `71` is `0.644062`, to six decimal places. -/
theorem absFiberSum_71 : |absFiberSum 71 256 - 0.644062| ≤ 1e-6 := by
  have he := absFiberSum_71_eq
  have h71 := absApprox_71
  rw [he]
  simp only [abs_le] at *
  constructor <;> norm_num <;> linarith [h71.1, h71.2]

end FiberSums
