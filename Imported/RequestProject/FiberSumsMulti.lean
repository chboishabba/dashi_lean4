/-
# Fiber sums of the primes with several powers in range (`p = 2, 3, 5, 7, 11, 13`)

For these six primes the fiber `{p^k ≤ 256}` has more than one point, so the signed and the
absolute fiber sums of `RequestProject/FiberSums.lean` genuinely differ.  Each value is pinned
down to six decimal places; each individual normalised coefficient `τ(n)/n^{11/2}` is first
located to nine decimal places from rational bounds `a ≤ √(n¹¹) ≤ b` on the denominator.
-/
import RequestProject.FiberSums

namespace FiberSums

open PrimeFibers RamanujanTau

/-! ### The fiber of `2`: the powers 2, 4, 8, 16, 32, 64, 128, 256 -/

private theorem approx_2 : |normTau 2 - (-0.530330085890)| ≤ 1e-9 :=
  normTau_approx (n := 2) (t := -24) (by native_decide) (a := 45.254833995939)
    (b := 45.254833995940) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

private theorem approx_4 : |normTau 4 - (-0.718750000000)| ≤ 1e-9 :=
  normTau_approx (n := 4) (t := -1472) (by native_decide) (a := 2048.000000000000)
    (b := 2048.000000000001) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

private theorem approx_8 : |normTau 8 - 0.911504835123| ≤ 1e-9 :=
  normTau_approx (n := 8) (t := 84480) (by native_decide) (a := 92681.900023683157)
    (b := 92681.900023683158) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

private theorem approx_16 : |normTau 16 - 0.235351562500| ≤ 1e-9 :=
  normTau_approx (n := 16) (t := 987136) (by native_decide) (a := 4194304.000000000000)
    (b := 4194304.000000000001) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

private theorem approx_32 : |normTau 32 - (-1.036318849478)| ≤ 1e-9 :=
  normTau_approx (n := 32) (t := -196706304) (by native_decide) (a := 189812531.248503105778)
    (b := 189812531.248503105779) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

private theorem approx_64 : |normTau 64 - 0.314239501953| ≤ 1e-9 :=
  normTau_approx (n := 64) (t := 2699296768) (by native_decide) (a := 8589934592.000000000000)
    (b := 8589934592.000000000001) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

private theorem approx_128 : |normTau 128 - 0.869668187417| ≤ 1e-9 :=
  normTau_approx (n := 128) (t := 338071388160) (by native_decide) (a := 388736063996.934360633777)
    (b := 388736063996.934360633778) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

private theorem approx_256 : |normTau 256 - (-0.775450706482)| ≤ 1e-9 :=
  normTau_approx (n := 256) (t := -13641873096704) (by native_decide) (a := 17592186044416.000000000000)
    (b := 17592186044416.000000000001) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem absApprox_2 : |(|normTau 2| - 0.530330085890)| ≤ 1e-9 := by
  have h := abs_approx_of_approx approx_2
  rwa [show |((-0.530330085890) : ℝ)| = 0.530330085890 from by norm_num] at h

theorem absApprox_4 : |(|normTau 4| - 0.718750000000)| ≤ 1e-9 := by
  have h := abs_approx_of_approx approx_4
  rwa [show |((-0.718750000000) : ℝ)| = 0.718750000000 from by norm_num] at h

theorem absApprox_8 : |(|normTau 8| - 0.911504835123)| ≤ 1e-9 := by
  have h := abs_approx_of_approx approx_8
  rwa [show |(0.911504835123 : ℝ)| = 0.911504835123 from by norm_num] at h

theorem absApprox_16 : |(|normTau 16| - 0.235351562500)| ≤ 1e-9 := by
  have h := abs_approx_of_approx approx_16
  rwa [show |(0.235351562500 : ℝ)| = 0.235351562500 from by norm_num] at h

theorem absApprox_32 : |(|normTau 32| - 1.036318849478)| ≤ 1e-9 := by
  have h := abs_approx_of_approx approx_32
  rwa [show |((-1.036318849478) : ℝ)| = 1.036318849478 from by norm_num] at h

theorem absApprox_64 : |(|normTau 64| - 0.314239501953)| ≤ 1e-9 := by
  have h := abs_approx_of_approx approx_64
  rwa [show |(0.314239501953 : ℝ)| = 0.314239501953 from by norm_num] at h

theorem absApprox_128 : |(|normTau 128| - 0.869668187417)| ≤ 1e-9 := by
  have h := abs_approx_of_approx approx_128
  rwa [show |(0.869668187417 : ℝ)| = 0.869668187417 from by norm_num] at h

theorem absApprox_256 : |(|normTau 256| - 0.775450706482)| ≤ 1e-9 := by
  have h := abs_approx_of_approx approx_256
  rwa [show |((-0.775450706482) : ℝ)| = 0.775450706482 from by norm_num] at h

/-- The fiber sum of `2`, written out over its 8 powers. -/
theorem signedFiberSum_2_eq : signedFiberSum 2 256 = normTau 2 + normTau 4 + normTau 8 + normTau 16 + normTau 32 + normTau 64 + normTau 128 + normTau 256 := by
  rw [signedFiberSum, sum_primePowerFiber _ (by norm_num) (by norm_num),
    show Nat.log 2 256 = 8 from by decide]
  norm_num [Finset.sum_Icc_succ_top]

/-- The absolute fiber sum of `2`, written out over its 8 powers. -/
theorem absFiberSum_2_eq : absFiberSum 2 256 = |normTau 2| + |normTau 4| + |normTau 8| + |normTau 16| + |normTau 32| + |normTau 64| + |normTau 128| + |normTau 256| := by
  rw [absFiberSum, sum_primePowerFiber _ (by norm_num) (by norm_num),
    show Nat.log 2 256 = 8 from by decide]
  norm_num [Finset.sum_Icc_succ_top]

/-- The signed fiber sum of `2` is `-0.730086`, to six decimal places. -/
theorem signedFiberSum_2 : |signedFiberSum 2 256 - (-0.730086)| ≤ 1e-6 := by
  have he := signedFiberSum_2_eq
  have h2 := approx_2
  have h4 := approx_4
  have h8 := approx_8
  have h16 := approx_16
  have h32 := approx_32
  have h64 := approx_64
  have h128 := approx_128
  have h256 := approx_256
  rw [he]
  simp only [abs_le] at *
  constructor <;> norm_num <;> linarith [h2.1, h2.2, h4.1, h4.2, h8.1, h8.2, h16.1, h16.2, h32.1, h32.2, h64.1, h64.2, h128.1, h128.2, h256.1, h256.2]

/-- The absolute fiber sum of `2` is `5.391614`, to six decimal places. -/
theorem absFiberSum_2 : |absFiberSum 2 256 - 5.391614| ≤ 1e-6 := by
  have he := absFiberSum_2_eq
  have h2 := absApprox_2
  have h4 := absApprox_4
  have h8 := absApprox_8
  have h16 := absApprox_16
  have h32 := absApprox_32
  have h64 := absApprox_64
  have h128 := absApprox_128
  have h256 := absApprox_256
  rw [he]
  simp only [abs_le] at *
  constructor <;> norm_num <;> linarith [h2.1, h2.2, h4.1, h4.2, h8.1, h8.2, h16.1, h16.2, h32.1, h32.2, h64.1, h64.2, h128.1, h128.2, h256.1, h256.2]

/-! ### The fiber of `3`: the powers 3, 9, 27, 81, 243 -/

private theorem approx_3 : |normTau 3 - 0.598733612493| ≤ 1e-9 :=
  normTau_approx (n := 3) (t := 252) (by native_decide) (a := 420.888346239237)
    (b := 420.888346239238) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

private theorem approx_9 : |normTau 9 - (-0.641518061271)| ≤ 1e-9 :=
  normTau_approx (n := 9) (t := -113643) (by native_decide) (a := 177147.000000000000)
    (b := 177147.000000000001) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

private theorem approx_27 : |normTau 27 - (-0.982832038797)| ≤ 1e-9 :=
  normTau_approx (n := 27) (t := -73279080) (by native_decide) (a := 74559107.871242149137)
    (b := 74559107.871242149138) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

private theorem approx_81 : |normTau 81 - 0.053063484208| ≤ 1e-9 :=
  normTau_approx (n := 81) (t := 1665188361) (by native_decide) (a := 31381059609.000000000000)
    (b := 31381059609.000000000001) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

private theorem approx_243 : |normTau 243 - 1.014602930389| ≤ 1e-9 :=
  normTau_approx (n := 243) (t := 13400796651732) (by native_decide) (a := 13207922282066.932993298106)
    (b := 13207922282066.932993298107) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem absApprox_3 : |(|normTau 3| - 0.598733612493)| ≤ 1e-9 := by
  have h := abs_approx_of_approx approx_3
  rwa [show |(0.598733612493 : ℝ)| = 0.598733612493 from by norm_num] at h

theorem absApprox_9 : |(|normTau 9| - 0.641518061271)| ≤ 1e-9 := by
  have h := abs_approx_of_approx approx_9
  rwa [show |((-0.641518061271) : ℝ)| = 0.641518061271 from by norm_num] at h

theorem absApprox_27 : |(|normTau 27| - 0.982832038797)| ≤ 1e-9 := by
  have h := abs_approx_of_approx approx_27
  rwa [show |((-0.982832038797) : ℝ)| = 0.982832038797 from by norm_num] at h

theorem absApprox_81 : |(|normTau 81| - 0.053063484208)| ≤ 1e-9 := by
  have h := abs_approx_of_approx approx_81
  rwa [show |(0.053063484208 : ℝ)| = 0.053063484208 from by norm_num] at h

theorem absApprox_243 : |(|normTau 243| - 1.014602930389)| ≤ 1e-9 := by
  have h := abs_approx_of_approx approx_243
  rwa [show |(1.014602930389 : ℝ)| = 1.014602930389 from by norm_num] at h

/-- The fiber sum of `3`, written out over its 5 powers. -/
theorem signedFiberSum_3_eq : signedFiberSum 3 256 = normTau 3 + normTau 9 + normTau 27 + normTau 81 + normTau 243 := by
  rw [signedFiberSum, sum_primePowerFiber _ (by norm_num) (by norm_num),
    show Nat.log 3 256 = 5 from by decide]
  norm_num [Finset.sum_Icc_succ_top]

/-- The absolute fiber sum of `3`, written out over its 5 powers. -/
theorem absFiberSum_3_eq : absFiberSum 3 256 = |normTau 3| + |normTau 9| + |normTau 27| + |normTau 81| + |normTau 243| := by
  rw [absFiberSum, sum_primePowerFiber _ (by norm_num) (by norm_num),
    show Nat.log 3 256 = 5 from by decide]
  norm_num [Finset.sum_Icc_succ_top]

/-- The signed fiber sum of `3` is `0.042050`, to six decimal places. -/
theorem signedFiberSum_3 : |signedFiberSum 3 256 - 0.042050| ≤ 1e-6 := by
  have he := signedFiberSum_3_eq
  have h3 := approx_3
  have h9 := approx_9
  have h27 := approx_27
  have h81 := approx_81
  have h243 := approx_243
  rw [he]
  simp only [abs_le] at *
  constructor <;> norm_num <;> linarith [h3.1, h3.2, h9.1, h9.2, h27.1, h27.2, h81.1, h81.2, h243.1, h243.2]

/-- The absolute fiber sum of `3` is `3.290750`, to six decimal places. -/
theorem absFiberSum_3 : |absFiberSum 3 256 - 3.290750| ≤ 1e-6 := by
  have he := absFiberSum_3_eq
  have h3 := absApprox_3
  have h9 := absApprox_9
  have h27 := absApprox_27
  have h81 := absApprox_81
  have h243 := absApprox_243
  rw [he]
  simp only [abs_le] at *
  constructor <;> norm_num <;> linarith [h3.1, h3.2, h9.1, h9.2, h27.1, h27.2, h81.1, h81.2, h243.1, h243.2]

/-! ### The fiber of `5`: the powers 5, 25, 125 -/

private theorem approx_5 : |normTau 5 - 0.691213333205| ≤ 1e-9 :=
  normTau_approx (n := 5) (t := 4830) (by native_decide) (a := 6987.712429686842)
    (b := 6987.712429686843) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

private theorem approx_25 : |normTau 25 - (-0.522224128000)| ≤ 1e-9 :=
  normTau_approx (n := 25) (t := -25499225) (by native_decide) (a := 48828125.000000000000)
    (b := 48828125.000000000001) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

private theorem approx_125 : |normTau 125 - (-1.052181613400)| ≤ 1e-9 :=
  normTau_approx (n := 125) (t := -359001100500) (by native_decide) (a := 341196895980.802871156184)
    (b := 341196895980.802871156185) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem absApprox_5 : |(|normTau 5| - 0.691213333205)| ≤ 1e-9 := by
  have h := abs_approx_of_approx approx_5
  rwa [show |(0.691213333205 : ℝ)| = 0.691213333205 from by norm_num] at h

theorem absApprox_25 : |(|normTau 25| - 0.522224128000)| ≤ 1e-9 := by
  have h := abs_approx_of_approx approx_25
  rwa [show |((-0.522224128000) : ℝ)| = 0.522224128000 from by norm_num] at h

theorem absApprox_125 : |(|normTau 125| - 1.052181613400)| ≤ 1e-9 := by
  have h := abs_approx_of_approx approx_125
  rwa [show |((-1.052181613400) : ℝ)| = 1.052181613400 from by norm_num] at h

/-- The fiber sum of `5`, written out over its 3 powers. -/
theorem signedFiberSum_5_eq : signedFiberSum 5 256 = normTau 5 + normTau 25 + normTau 125 := by
  rw [signedFiberSum, sum_primePowerFiber _ (by norm_num) (by norm_num),
    show Nat.log 5 256 = 3 from by decide]
  norm_num [Finset.sum_Icc_succ_top]

/-- The absolute fiber sum of `5`, written out over its 3 powers. -/
theorem absFiberSum_5_eq : absFiberSum 5 256 = |normTau 5| + |normTau 25| + |normTau 125| := by
  rw [absFiberSum, sum_primePowerFiber _ (by norm_num) (by norm_num),
    show Nat.log 5 256 = 3 from by decide]
  norm_num [Finset.sum_Icc_succ_top]

/-- The signed fiber sum of `5` is `-0.883192`, to six decimal places. -/
theorem signedFiberSum_5 : |signedFiberSum 5 256 - (-0.883192)| ≤ 1e-6 := by
  have he := signedFiberSum_5_eq
  have h5 := approx_5
  have h25 := approx_25
  have h125 := approx_125
  rw [he]
  simp only [abs_le] at *
  constructor <;> norm_num <;> linarith [h5.1, h5.2, h25.1, h25.2, h125.1, h125.2]

/-- The absolute fiber sum of `5` is `2.265619`, to six decimal places. -/
theorem absFiberSum_5 : |absFiberSum 5 256 - 2.265619| ≤ 1e-6 := by
  have he := absFiberSum_5_eq
  have h5 := absApprox_5
  have h25 := absApprox_25
  have h125 := absApprox_125
  rw [he]
  simp only [abs_le] at *
  constructor <;> norm_num <;> linarith [h5.1, h5.2, h25.1, h25.2, h125.1, h125.2]

/-! ### The fiber of `7`: the powers 7, 49 -/

private theorem approx_7 : |normTau 7 - (-0.376547696559)| ≤ 1e-9 :=
  normTau_approx (n := 7) (t := -16744) (by native_decide) (a := 44467.142285062574)
    (b := 44467.142285062575) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

private theorem approx_49 : |normTau 49 - (-0.858211832216)| ≤ 1e-9 :=
  normTau_approx (n := 49) (t := -1696965207) (by native_decide) (a := 1977326743.000000000000)
    (b := 1977326743.000000000001) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem absApprox_7 : |(|normTau 7| - 0.376547696559)| ≤ 1e-9 := by
  have h := abs_approx_of_approx approx_7
  rwa [show |((-0.376547696559) : ℝ)| = 0.376547696559 from by norm_num] at h

theorem absApprox_49 : |(|normTau 49| - 0.858211832216)| ≤ 1e-9 := by
  have h := abs_approx_of_approx approx_49
  rwa [show |((-0.858211832216) : ℝ)| = 0.858211832216 from by norm_num] at h

/-- The fiber sum of `7`, written out over its 2 powers. -/
theorem signedFiberSum_7_eq : signedFiberSum 7 256 = normTau 7 + normTau 49 := by
  rw [signedFiberSum, sum_primePowerFiber _ (by norm_num) (by norm_num),
    show Nat.log 7 256 = 2 from by decide]
  norm_num [Finset.sum_Icc_succ_top]

/-- The absolute fiber sum of `7`, written out over its 2 powers. -/
theorem absFiberSum_7_eq : absFiberSum 7 256 = |normTau 7| + |normTau 49| := by
  rw [absFiberSum, sum_primePowerFiber _ (by norm_num) (by norm_num),
    show Nat.log 7 256 = 2 from by decide]
  norm_num [Finset.sum_Icc_succ_top]

/-- The signed fiber sum of `7` is `-1.234760`, to six decimal places. -/
theorem signedFiberSum_7 : |signedFiberSum 7 256 - (-1.234760)| ≤ 1e-6 := by
  have he := signedFiberSum_7_eq
  have h7 := approx_7
  have h49 := approx_49
  rw [he]
  simp only [abs_le] at *
  constructor <;> norm_num <;> linarith [h7.1, h7.2, h49.1, h49.2]

/-- The absolute fiber sum of `7` is `1.234760`, to six decimal places. -/
theorem absFiberSum_7 : |absFiberSum 7 256 - 1.234760| ≤ 1e-6 := by
  have he := absFiberSum_7_eq
  have h7 := absApprox_7
  have h49 := absApprox_49
  rw [he]
  simp only [abs_le] at *
  constructor <;> norm_num <;> linarith [h7.1, h7.2, h49.1, h49.2]

/-! ### The fiber of `11`: the powers 11, 121 -/

private theorem approx_11 : |normTau 11 - 1.000872909497| ≤ 1e-9 :=
  normTau_approx (n := 11) (t := 534612) (by native_decide) (a := 534145.739111527501)
    (b := 534145.739111527502) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

private theorem approx_121 : |normTau 121 - 0.001746580965| ≤ 1e-9 :=
  normTau_approx (n := 121) (t := 498319933) (by native_decide) (a := 285311670611.000000000000)
    (b := 285311670611.000000000001) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem absApprox_11 : |(|normTau 11| - 1.000872909497)| ≤ 1e-9 := by
  have h := abs_approx_of_approx approx_11
  rwa [show |(1.000872909497 : ℝ)| = 1.000872909497 from by norm_num] at h

theorem absApprox_121 : |(|normTau 121| - 0.001746580965)| ≤ 1e-9 := by
  have h := abs_approx_of_approx approx_121
  rwa [show |(0.001746580965 : ℝ)| = 0.001746580965 from by norm_num] at h

/-- The fiber sum of `11`, written out over its 2 powers. -/
theorem signedFiberSum_11_eq : signedFiberSum 11 256 = normTau 11 + normTau 121 := by
  rw [signedFiberSum, sum_primePowerFiber _ (by norm_num) (by norm_num),
    show Nat.log 11 256 = 2 from by decide]
  norm_num [Finset.sum_Icc_succ_top]

/-- The absolute fiber sum of `11`, written out over its 2 powers. -/
theorem absFiberSum_11_eq : absFiberSum 11 256 = |normTau 11| + |normTau 121| := by
  rw [absFiberSum, sum_primePowerFiber _ (by norm_num) (by norm_num),
    show Nat.log 11 256 = 2 from by decide]
  norm_num [Finset.sum_Icc_succ_top]

/-- The signed fiber sum of `11` is `1.002619`, to six decimal places. -/
theorem signedFiberSum_11 : |signedFiberSum 11 256 - 1.002619| ≤ 1e-6 := by
  have he := signedFiberSum_11_eq
  have h11 := approx_11
  have h121 := approx_121
  rw [he]
  simp only [abs_le] at *
  constructor <;> norm_num <;> linarith [h11.1, h11.2, h121.1, h121.2]

/-- The absolute fiber sum of `11` is `1.002619`, to six decimal places. -/
theorem absFiberSum_11 : |absFiberSum 11 256 - 1.002619| ≤ 1e-6 := by
  have he := absFiberSum_11_eq
  have h11 := absApprox_11
  have h121 := absApprox_121
  rw [he]
  simp only [abs_le] at *
  constructor <;> norm_num <;> linarith [h11.1, h11.2, h121.1, h121.2]

/-! ### The fiber of `13`: the powers 13, 169 -/

private theorem approx_13 : |normTau 13 - (-0.431561303293)| ≤ 1e-9 :=
  normTau_approx (n := 13) (t := -577738) (by native_decide) (a := 1338715.949720850976)
    (b := 1338715.949720850977) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

private theorem approx_169 : |normTau 169 - (-0.813754841500)| ≤ 1e-9 :=
  normTau_approx (n := 169) (t := -1458379197393) (by native_decide) (a := 1792160394037.000000000000)
    (b := 1792160394037.000000000001) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem absApprox_13 : |(|normTau 13| - 0.431561303293)| ≤ 1e-9 := by
  have h := abs_approx_of_approx approx_13
  rwa [show |((-0.431561303293) : ℝ)| = 0.431561303293 from by norm_num] at h

theorem absApprox_169 : |(|normTau 169| - 0.813754841500)| ≤ 1e-9 := by
  have h := abs_approx_of_approx approx_169
  rwa [show |((-0.813754841500) : ℝ)| = 0.813754841500 from by norm_num] at h

/-- The fiber sum of `13`, written out over its 2 powers. -/
theorem signedFiberSum_13_eq : signedFiberSum 13 256 = normTau 13 + normTau 169 := by
  rw [signedFiberSum, sum_primePowerFiber _ (by norm_num) (by norm_num),
    show Nat.log 13 256 = 2 from by decide]
  norm_num [Finset.sum_Icc_succ_top]

/-- The absolute fiber sum of `13`, written out over its 2 powers. -/
theorem absFiberSum_13_eq : absFiberSum 13 256 = |normTau 13| + |normTau 169| := by
  rw [absFiberSum, sum_primePowerFiber _ (by norm_num) (by norm_num),
    show Nat.log 13 256 = 2 from by decide]
  norm_num [Finset.sum_Icc_succ_top]

/-- The signed fiber sum of `13` is `-1.245316`, to six decimal places. -/
theorem signedFiberSum_13 : |signedFiberSum 13 256 - (-1.245316)| ≤ 1e-6 := by
  have he := signedFiberSum_13_eq
  have h13 := approx_13
  have h169 := approx_169
  rw [he]
  simp only [abs_le] at *
  constructor <;> norm_num <;> linarith [h13.1, h13.2, h169.1, h169.2]

/-- The absolute fiber sum of `13` is `1.245316`, to six decimal places. -/
theorem absFiberSum_13 : |absFiberSum 13 256 - 1.245316| ≤ 1e-6 := by
  have he := absFiberSum_13_eq
  have h13 := absApprox_13
  have h169 := absApprox_169
  rw [he]
  simp only [abs_le] at *
  constructor <;> norm_num <;> linarith [h13.1, h13.2, h169.1, h169.2]

end FiberSums
