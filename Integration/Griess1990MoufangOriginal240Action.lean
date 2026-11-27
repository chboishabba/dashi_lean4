import Integration.Griess1990OriginalT5Moufang243240Chart
import Integration.Griess1990Moufang81ElementaryLift
import Mathlib

/-!
# Genuine source-derived Moufang81 action on the ORIGINAL 240 T5 cut

Consumes the exact *same-object*, explicitly inverted chart
  OldRelativeT5 ≃ (M81 \ {identity}) × F3
from Griess1990OriginalT5Moufang243240Chart, and the six
Griess-source g-corrected loop automorphisms from
Griess1990Moufang81ElementaryLift.

Unlike the earlier count 240=E8 roots, this is a mathematically
honest ACTION on the original 240 old states. It is nonlinear in
the original five-trit coordinates, does not preserve the old open
path-cube adjacency or the original E6/W(E8) quadratic action,
and is NOT identified as the existing exceptional E8 carrier.

Primary external source: R. L. Griess Jr. (1990), J Algebra 131,
281-293 DOI 10.1016/0021-8693(90)90176-O.
The 243/240 complement owner is DASHI Lean #43/Agda #1094.
Formal implementation is SOURCE-WRITTEN, Lean kernel NOT RUN.
-/

namespace Integration.Griess1990MoufangOriginal240Action

open Integration.Griess1990OriginalT5Moufang243240Chart
open Integration.Griess1990Moufang81Determinant
open Integration.Griess1990Moufang81ElementaryLift

/-- The M81 shear on the genuine nonidentity loop carrier; the
unchanged extra central chart coordinate is NOT a loop product. -/
def puncturedShear (s : Shear) :
    PuncturedM81 × ZMod 3 → PuncturedM81 × ZMod 3
  | (m,t) =>
      (⟨lift s m.1, six_lifts_preserve_nonidentity s m.1 m.2⟩, t)

/-- Original five-trit 240-state carrier action transported across
the LITERAL source chart, not invented from cardinality. -/
def actOnOriginal240 (s : Shear) (z : Old240) : Old240 :=
  old240EquivPuncturedM81TimesF3.symm
    (puncturedShear s (old240EquivPuncturedM81TimesF3 z))

/-- Concrete source/action intertwiner on all 240 original states. -/
theorem exact_chart_intertwines_actual_m81_shears :
    ∀ s : Shear, ∀ z : Old240,
      old240EquivPuncturedM81TimesF3 (actOnOriginal240 s z) =
        puncturedShear s (old240EquivPuncturedM81TimesF3 z) := by
  intro s z
  exact old240EquivPuncturedM81TimesF3.apply_symm_apply _

theorem source_selected_shears_order_three_on_original240 :
    ∀ s : Shear, ∀ z : Old240,
      actOnOriginal240 s (actOnOriginal240 s (actOnOriginal240 s z)) = z := by
  native_decide

/-- The original source M81 multiplication is paid by the
unpunctured actor upstream; this theorem transports the action only.
The E6 reflection s3 counterexample remains in force on the SAME T5. -/
theorem existing_e6_s3_still_not_an_old240_endomorphism :
    ¬ (∀ s (z : Old240), ¬ OldDiagonal
        (Integration.E6Mod3WeylAction.reflectStandard s z.1)) :=
  original240_inherited_E6_action_blocked

end Integration.Griess1990MoufangOriginal240Action
