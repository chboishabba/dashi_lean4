import Synthesis.MillenniumBSDCMGaloisHalfPointTableExact
import Synthesis.MillenniumBSDRationalQuadraticKummerDescent
import Synthesis.MillenniumBSDCMGlobalKummerCharacterCompilerExact
import Mathlib.Tactic

/-!
# Selected CM curve: explicit root signs are the paid scalar Kummer bits

For an ordinary rational point P=(x,y), choose explicit Qbar roots

  a²=x, b²=x-1, c²=x+1, abc=-y.

The scalar quadratic Kummer character was defined using a canonical chosen
square root.  Root-choice invariance already proves that its bit is unchanged
if that canonical root is replaced by the explicit half roots a or b.  Hence
the raw geometric coordinate order `(bit b, bit a)` is literally the pair of
paid scalar Kummer characters `(χ_{x-1},χ_x)`.
-/

namespace Synthesis.Millennium.BSD

noncomputable section

/-- The canonical scalar Kummer bit for x agrees with the sign bit of any
explicit Qbar square root a of x. -/
theorem rationalKummerBit_eq_explicitRoot
    (σ : RationalAbsoluteGalois)
    {x : ℚ} (hx0 : x ≠ 0)
    {a : RatAlgClosure}
    (ha : a ^ 2 = (x : RatAlgClosure)) :
    rationalKummerBit ⟨x, hx0⟩ σ =
      rationalKummerBitOfRoot a σ := by
  rw [rationalKummerBit_eq_ofRoot]
  apply rationalKummerBitOfRoot_independent
  calc
    rationalKummerRoot ⟨x, hx0⟩ * rationalKummerRoot ⟨x, hx0⟩ =
        (x : RatAlgClosure) := rationalKummerRoot_spec ⟨x, hx0⟩
    _ = a * a := by simpa [pow_two] using ha.symm

/-- Same root-choice statement for x-1. -/
theorem rationalKummerBit_sub_one_eq_explicitRoot
    (σ : RationalAbsoluteGalois)
    {x : ℚ} (hx1 : x ≠ 1)
    {b : RatAlgClosure}
    (hb : b ^ 2 = (x : RatAlgClosure) - 1) :
    rationalKummerBit ⟨x - 1, sub_ne_zero.mpr hx1⟩ σ =
      rationalKummerBitOfRoot b σ := by
  rw [rationalKummerBit_eq_ofRoot]
  apply rationalKummerBitOfRoot_independent
  calc
    rationalKummerRoot ⟨x - 1, sub_ne_zero.mpr hx1⟩ *
        rationalKummerRoot ⟨x - 1, sub_ne_zero.mpr hx1⟩ =
      ((x - 1 : ℚ) : RatAlgClosure) :=
        rationalKummerRoot_spec ⟨x - 1, sub_ne_zero.mpr hx1⟩
    _ = b * b := by
      norm_num at hb ⊢
      simpa [pow_two] using hb.symm

/-- The paid raw geometric character pair evaluates pointwise as the explicit
root-sign pair `(bit b, bit a)`. -/
theorem cmRawGeometricQuadraticCharacterPair_apply_bits
    (σ : RationalAbsoluteGalois)
    {x : ℚ} (hx0 : x ≠ 0) (hx1 : x ≠ 1)
    {a b : RatAlgClosure}
    (ha : a ^ 2 = (x : RatAlgClosure))
    (hb : b ^ 2 = (x : RatAlgClosure) - 1) :
    (Multiplicative.toAdd
        ((cmRawGeometricQuadraticCharacterPair x hx0 hx1).1 σ),
      Multiplicative.toAdd
        ((cmRawGeometricQuadraticCharacterPair x hx0 hx1).2 σ)) =
      (rationalKummerBitOfRoot b σ,
        rationalKummerBitOfRoot a σ) := by
  apply Prod.ext
  · exact rationalKummerBit_sub_one_eq_explicitRoot σ hx1 hb
  · exact rationalKummerBit_eq_explicitRoot σ hx0 ha

/-!
MAX-CUT STATUS

PAID HERE, subject to exact-head kernel certification:
* canonical Kummer-root choice is removed from both ordinary x-T coordinates;
* the paid scalar characters evaluate exactly as the explicit half root signs;
* the raw geometric orientation is therefore `(bit b, bit a)` with no
  remaining square-class or Hilbert-90 argument.

THE SOLE ORDINARY-POINT GLOBAL WELD LEFT IS NOW A SAME-OBJECT TRANSPORT LEMMA:
show that `cmGeometricKummerTrivialCharacter` evaluated on the explicit half,
after the already-paid generic-E[2] -> actual-E[2] -> `(Z/2)^2` equivalences,
is exactly `(bit b,bit a)`.  The four actual point cases proving the value are
already in `MillenniumBSDCMGaloisHalfPointTableExact`.
-/

end

end Synthesis.Millennium.BSD
