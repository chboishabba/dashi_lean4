import Integration.Kernel.Quotient

/-!
# Bridge: phase coherence ↔ corroboration quality beyond source count

The third narrow bridge.  The donor observation is that a signal built from many
contributions can be strong or weak depending on whether the contributions are
in phase, and that adding a contribution can *reduce* the result.  Transported
to corroboration, the content is that a count of reports is not a measure of
support, because reports carry a direction.

## What is proved

* `net`, `count` — the signed sum of a list of reports and its length.
* **`more_reports_less_support`** — an explicit pair: appending a report raises
  the count and lowers the absolute net support.
* **`support_does_not_descend_through_count`** — hence no function of the number
  of reports returns the support: `Integration.Kernel.Quotient` again.
* `inPhase_net_eq_count` — the positive half: when every report points the same
  way, support and count do coincide, which is exactly the special case in which
  counting is legitimate.
* **`coherent_pair_beats_incoherent_quartet`** — two aligned reports carry more
  net support than four mixed ones.

**Claim boundary.**  A report is an element of `ℤ` with values `±1`, and
"support" is their sum.  Nothing models any measurement, source, publication or
degree of belief.
-/

namespace Integration.Kernel.Bridges.CorroborationPhase

open Integration.Kernel.Quotient

/-- The net support of a list of signed reports. -/
def net (rs : List ℤ) : ℤ := rs.sum

/-- How many reports there are. -/
def count (rs : List ℤ) : ℕ := rs.length

/-- Every report points the same way. -/
def InPhase (rs : List ℤ) : Prop := ∀ r ∈ rs, r = 1

/-- Three aligned reports. -/
def aligned : List ℤ := [1, 1, 1]

/-- The same three with one opposing report appended. -/
def mixed : List ℤ := [1, 1, 1, -1]

/-- **A further report can lower the support it is added to.** -/
theorem more_reports_less_support :
    count mixed = count aligned + 1 ∧ net mixed < net aligned := by
  refine ⟨rfl, by decide⟩

/-- **Support is not a function of the number of reports.** -/
theorem support_does_not_descend_through_count :
    ¬ DescendsThrough net count :=
  not_descendsThrough_of_collision (x := ([1, -1] : List ℤ)) (y := ([1, 1] : List ℤ))
    rfl (by decide)

/-- When the reports are in phase, support is the count. -/
theorem inPhase_net_eq_count {rs : List ℤ} (h : InPhase rs) : net rs = (count rs : ℤ) := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
      have hr : r = 1 := h r (List.mem_cons_self ..)
      have hrest : InPhase rs := fun x hx => h x (List.mem_cons_of_mem _ hx)
      have hih : rs.sum = (rs.length : ℤ) := ih hrest
      show (r :: rs).sum = (((r :: rs).length : ℕ) : ℤ)
      rw [List.sum_cons, hr, hih, List.length_cons]
      push_cast
      ring

/-- **Two coherent reports outweigh four incoherent ones.** -/
theorem coherent_pair_beats_incoherent_quartet :
    count [1, 1] < count [1, -1, 1, -1] ∧ net [1, -1, 1, -1] < net [1, 1] := by
  refine ⟨by decide, by decide⟩

end Integration.Kernel.Bridges.CorroborationPhase
