import RequestProject.SeriesChain

/-!
# A worked series: a three-volume book series

A concrete fragment exercising `RequestProject.Series` and `RequestProject.SeriesChain`: a
book series `t` with three volumes, each declared `part of the series` `t`, chained by
`follows` (P155) statements and numbered by `series ordinal` (P1545) values.  Everything
here is decided by computation, including the defects the validator is meant to catch: a
cyclic series, a forking series, and ordinals disagreeing with the `follows` statements.
-/

namespace Wikidata
namespace SKB

/-! ### A worked example: a three-volume book series

The series `t` (an instance of `book series`, Q277759) has three volumes `v1`, `v2`, `v3`
(instances of `literary work`, Q7725634), each declared `part of the series` `t`, with
`v2` following `v1`, `v3` following `v2`, and `series ordinal` values `1`, `2`, `3`. -/

/-- The taxonomy underlying the worked example. -/
def trilogyBase : KB where
  name := "trilogy"
  items := [Qid.wd "Q277759", Qid.wd "Q7725634", Qid.wd "t",
            Qid.wd "v1", Qid.wd "v2", Qid.wd "v3"]
  levels := [(Qid.wd "Q277759", 1), (Qid.wd "Q7725634", 1)]
  inst := [(Qid.wd "t", Qid.wd "Q277759"), (Qid.wd "v1", Qid.wd "Q7725634"),
           (Qid.wd "v2", Qid.wd "Q7725634"), (Qid.wd "v3", Qid.wd "Q7725634")]

/-- The worked series layer. -/
def trilogySKB : SKB where
  base := trilogyBase
  series := [(Qid.wd "v1", Qid.wd "t"), (Qid.wd "v2", Qid.wd "t"),
             (Qid.wd "v3", Qid.wd "t")]
  follows := [(Qid.wd "v2", Qid.wd "v1"), (Qid.wd "v3", Qid.wd "v2")]
  ordinals := [(Qid.wd "v1", 1), (Qid.wd "v2", 2), (Qid.wd "v3", 3)]

/-- The worked example passes every check. -/
theorem trilogy_valid : trilogySKB.sValid = true := by decide

/-- Its ordinals are monotone and its successors are unique. -/
theorem trilogy_checks :
    trilogySKB.ordinalsMonotone = true ∧ trilogySKB.singleSuccessor = true := by decide

/-- Ordinals are, however, *not* total: the series item and the two classes carry no
`series ordinal`, which is exactly as it should be — only the members of a series are
ordered. -/
theorem trilogy_ordinals_not_total : trilogySKB.ordinalsTotal = false := by decide

/-- The third volume comes after the first, although nobody said so directly. -/
theorem trilogy_v3_after_v1 :
    trilogySKB.isStrictlyAfterB (Qid.wd "v3") (Qid.wd "v1") = true := by decide

/-- Yet the property layer makes no `follows` statement from the third volume to the
first: coming after is the transitive closure, `follows` itself is not transitive. -/
theorem trilogy_follows_not_transitive :
    ¬ trilogySKB.toPropertyLayer.Holds .follows (Qid.wd "v3") (Qid.wd "v1") := by
  intro h
  have := (holds_iff _ _ _ _).1 h
  simp [PropStmt, Follows, trilogySKB] at this

/-- …and not the other way round. -/
theorem trilogy_v1_not_after_v3 :
    trilogySKB.isAfterB (Qid.wd "v1") (Qid.wd "v3") = false := by decide

/-- The first volume is the unique origin of the series. -/
theorem trilogy_origin :
    trilogySKB.originsOfL (Qid.wd "v3") = [Qid.wd "v1"] := by decide

/-- Starting from the first volume, the chain enumerates the whole series in order. -/
theorem trilogy_chain :
    trilogySKB.chainFrom (Qid.wd "v1") =
      [Qid.wd "v1", Qid.wd "v2", Qid.wd "v3"] := by decide

/-- `followed by` (P156) is read off the same statements. -/
theorem trilogy_next : trilogySKB.nextL (Qid.wd "v1") = [Qid.wd "v2"] := by decide

/-- The members of the series. -/
theorem trilogy_members :
    trilogySKB.membersOfL (Qid.wd "t") = [Qid.wd "v1", Qid.wd "v2", Qid.wd "v3"] := by decide

/-- **Series membership is not inherited through `instance of`**: the volumes belong to
the series, but the class `literary work` they instantiate does not. -/
theorem trilogy_series_not_inherited :
    trilogySKB.seriesOfL (Qid.wd "Q7725634") = [] := by decide

/-- The same three volumes with the surrounding classes removed, so that *every* item
carries a `series ordinal`. -/
def volumesSKB : SKB where
  base := { name := "volumes", items := [Qid.wd "v1", Qid.wd "v2", Qid.wd "v3"] }
  follows := [(Qid.wd "v2", Qid.wd "v1"), (Qid.wd "v3", Qid.wd "v2")]
  ordinals := [(Qid.wd "v1", 1), (Qid.wd "v2", 2), (Qid.wd "v3", 3)]

theorem volumes_ordinal_checks :
    volumesSKB.sWellFormed = true ∧ volumesSKB.ordinalsMonotone = true ∧
      volumesSKB.ordinalsTotal = true := by decide

/-- The two local ordinal checks therefore certify, with no search through the `follows`
graph at all, that no volume comes strictly after itself. -/
theorem volumes_no_cycle (a : Qid) : ¬ Relation.TransGen volumesSKB.Follows a a :=
  no_cycle_of_ordinals (by decide) (by decide) (by decide) a

/-! ### The defects the checks catch -/

/-- A cyclic series — the first volume also declared to follow the third — is rejected. -/
theorem cyclic_series_rejected :
    { trilogySKB with
        follows := trilogySKB.follows ++ [(Qid.wd "v1", Qid.wd "v3")] }.sAcyclic = false := by
  decide

/-- A forking series — one volume following two different volumes — is rejected. -/
theorem forking_series_rejected :
    { trilogySKB with
        follows := trilogySKB.follows ++
          [(Qid.wd "v3", Qid.wd "v1")] }.singlePredecessor = false := by
  decide

/-- Ordinals disagreeing with the `follows` statements are rejected. -/
theorem bad_ordinals_rejected :
    { trilogySKB with
        ordinals := [(Qid.wd "v1", 3), (Qid.wd "v2", 2),
                     (Qid.wd "v3", 1)] }.ordinalsMonotone = false := by
  decide

end SKB

end Wikidata
