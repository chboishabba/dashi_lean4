/-
# §6 of the BIDI note: the marked stage and its resolvent defect

The single stage changed by the CMP99 domain/background replacement is estimated
by the second resolvent identity.  Everything here is proved in an arbitrary
normed ring from the four inverse equations, with no invertibility theory and no
completeness assumption: the two inverses are *given*, which is the situation in
the Round72 algebra where both propagators have already been constructed.

* `second_resolvent_identity` — `G_L − G_R = −(G_L · E · G_R)` (equation (15));
* `norm_resolvent_defect_le` — `‖G_L − G_R‖ ≤ ‖G_L‖·‖eDefect‖·‖G_R‖` (equation (16));
* `Stage.ofResolventDefect` and `valid_ofResolventDefect` — the marked stage in
  the form the telescope consumes, i.e. equation (17);
* `norm_self_sub_self_le_zero` — law (19), `‖A − A‖ ≤ 0`, the unchanged-stage
  law of equation (18)/(20).
-/
import Mathlib
import RequestProject.YangMills.BIDI.NoncommTelescope

namespace RequestProject.YangMills.BIDI

variable {R : Type*} [NormedRing R]

/-- **The second resolvent identity.**  If `G_R` is a two-sided inverse of `A`
and `G_L` is a two-sided inverse of `A + E`, then `G_L − G_R = −(G_L E G_R)`. -/
theorem second_resolvent_identity {a eDefect Gl Gr : R}
    (hRr : a * Gr = 1) (hLl : Gl * (a + eDefect) = 1) :
    Gl - Gr = -(Gl * eDefect * Gr) := by
  have h1 : Gl * (a * Gr) = Gl := by rw [hRr, mul_one]
  have h2 : (Gl * (a + eDefect)) * Gr = Gr := by rw [hLl, one_mul]
  have h3 : Gl * (a * Gr) - (Gl * (a + eDefect)) * Gr = -(Gl * eDefect * Gr) := by
    noncomm_ring
  rwa [h1, h2] at h3

/-- **The resolvent defect bound**, equation (16). -/
theorem norm_resolvent_defect_le {a eDefect Gl Gr : R}
    (hRr : a * Gr = 1) (hLl : Gl * (a + eDefect) = 1) :
    ‖Gl - Gr‖ ≤ ‖Gl‖ * ‖eDefect‖ * ‖Gr‖ := by
  rw [second_resolvent_identity hRr hLl, norm_neg]
  exact le_trans (norm_mul_le _ _) (mul_le_mul_of_nonneg_right (norm_mul_le _ _)
    (norm_nonneg _))

/-- **Law (19)**: a literally unchanged stage has zero defect. -/
theorem norm_self_sub_self_le_zero (a : R) : ‖a - a‖ ≤ 0 := by simp

/-- The marked stage produced by a CMP99 replacement: the two propagators, the
common ordinary bound `max ‖G_L‖ ‖G_R‖`, and the resolvent defect budget. -/
noncomputable def Stage.ofResolventDefect (eDefect Gl Gr : R) : Stage R where
  before := Gl
  after := Gr
  bound := max ‖Gl‖ ‖Gr‖
  defect := ‖Gl‖ * ‖eDefect‖ * ‖Gr‖

theorem valid_ofResolventDefect {a eDefect Gl Gr : R}
    (hRr : a * Gr = 1) (hLl : Gl * (a + eDefect) = 1) :
    (Stage.ofResolventDefect eDefect Gl Gr).Valid :=
  ⟨le_max_left _ _, le_max_right _ _, norm_resolvent_defect_le hRr hLl⟩

/-- A stage with a *declared* defect budget `m` dominating the resolvent
defect; this is the form (17) in which the CMP99 budget is quoted. -/
theorem valid_marked_of_le {a eDefect Gl Gr : R} {m : ℝ}
    (hRr : a * Gr = 1) (hLl : Gl * (a + eDefect) = 1)
    (hm : ‖Gl‖ * ‖eDefect‖ * ‖Gr‖ ≤ m) :
    (Stage.mk Gl Gr (max ‖Gl‖ ‖Gr‖) m).Valid :=
  ⟨le_max_left _ _, le_max_right _ _, le_trans (norm_resolvent_defect_le hRr hLl) hm⟩

end RequestProject.YangMills.BIDI
