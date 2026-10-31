import Mathlib

/-!
A **generic** Lean list-to-Finset CNF semantics donor, not a new SAT
implementation. In particular, it is not yet specialized to OpenAI 378's
newer `OAI.Algorithms.SubexponentialSAT.SAT.Literal (Fin n)` because the
DASHI vendor pin precedes that family. This is deliberately outside
Integration/OpenAIMath/Everything.lean until a pinned Lean kernel receipt.

Original mathematics: classical propositional set semantics / Cook-Levin,
and the original source Agda List-CNF owner in DASHI.
Proof authorship: new adapter source only. No stronger ETH result claimed.
-/

namespace Integration.OpenAIMath.ListFinsetCNFTransport

variable {Literal : Type*} [DecidableEq Literal]

def listClauseSatisfied
    (assignment : Literal → Bool) (clause : List Literal) : Prop :=
  ∃ literal ∈ clause, assignment literal = true

def finsetClauseSatisfied
    (assignment : Literal → Bool) (clause : Finset Literal) : Prop :=
  ∃ literal ∈ clause, assignment literal = true

def listCNFSatisfied
    (assignment : Literal → Bool) (formula : List (List Literal)) : Prop :=
  ∀ clause ∈ formula, listClauseSatisfied assignment clause

def finsetCNFSatisfied
    (assignment : Literal → Bool) (formula : Finset (Finset Literal)) : Prop :=
  ∀ clause ∈ formula, finsetClauseSatisfied assignment clause

def toFinsetCNF (formula : List (List Literal)) : Finset (Finset Literal) :=
  (formula.map List.toFinset).toFinset

theorem clauseSemanticsExact (assignment : Literal → Bool)
    (clause : List Literal) :
    listClauseSatisfied assignment clause ↔
      finsetClauseSatisfied assignment clause.toFinset := by
  simp [listClauseSatisfied, finsetClauseSatisfied]

theorem cnfSemanticsExact (assignment : Literal → Bool)
    (formula : List (List Literal)) :
    listCNFSatisfied assignment formula ↔
      finsetCNFSatisfied assignment (toFinsetCNF formula) := by
  constructor
  · intro h clause hclause
    have hmem : clause ∈ formula.map List.toFinset := by
      simpa [toFinsetCNF] using hclause
    rcases List.mem_map.mp hmem with ⟨sourceClause, hsource, heq⟩
    subst clause
    exact (clauseSemanticsExact assignment sourceClause).mp (h sourceClause hsource)
  · intro h clause hclause
    have hmem : clause.toFinset ∈ toFinsetCNF formula := by
      simp [toFinsetCNF, List.mem_map, hclause]
    exact (clauseSemanticsExact assignment clause).mpr
      (h clause.toFinset hmem)

theorem toFinsetCardAtMostListLength (source : List Literal) :
    source.toFinset.card ≤ source.length := by
  induction source with
  | nil => simp
  | cons head tail ih =>
    by_cases h : head ∈ tail.toFinset
    · simp [List.toFinset_cons, h]
      omega
    · simp [List.toFinset_cons, h]
      omega

theorem clauseNumberUpper (formula : List (List Literal)) :
    (toFinsetCNF formula).card ≤ formula.length := by
  simpa [toFinsetCNF] using
    (toFinsetCardAtMostListLength (source := formula.map List.toFinset))

theorem normalizedClauseWidthUpper
    (formula : List (List Literal)) (bound : Nat)
    (width : ∀ clause ∈ formula, clause.length ≤ bound) :
    ∀ clause ∈ toFinsetCNF formula, clause.card ≤ bound := by
  intro clause hclause
  have hmem : clause ∈ formula.map List.toFinset := by
    simpa [toFinsetCNF] using hclause
  rcases List.mem_map.mp hmem with ⟨sourceClause, hsource, heq⟩
  subst clause
  exact (toFinsetCardAtMostListLength sourceClause).trans
    (width sourceClause hsource)

noncomputable def countedListModels (n : Nat)
    (eval : Literal → (Fin n → Bool) → Bool)
    (formula : List (List Literal)) : Nat := by
  classical
  exact (Finset.univ.filter
    (fun a : Fin n → Bool =>
      listCNFSatisfied (fun literal => eval literal a) formula)).card

noncomputable def countedFinsetModels (n : Nat)
    (eval : Literal → (Fin n → Bool) → Bool)
    (formula : Finset (Finset Literal)) : Nat := by
  classical
  exact (Finset.univ.filter
    (fun a : Fin n → Bool =>
      finsetCNFSatisfied (fun literal => eval literal a) formula)).card

theorem normalizedModelCountExact (n : Nat)
    (eval : Literal → (Fin n → Bool) → Bool)
    (formula : List (List Literal)) :
    countedListModels n eval formula =
      countedFinsetModels n eval (toFinsetCNF formula) := by
  classical
  unfold countedListModels countedFinsetModels
  have setsEqual :
      (Finset.univ.filter
        (fun a : Fin n → Bool =>
          listCNFSatisfied (fun literal => eval literal a) formula)) =
      (Finset.univ.filter
        (fun a : Fin n → Bool =>
          finsetCNFSatisfied (fun literal => eval literal a)
            (toFinsetCNF formula))) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact cnfSemanticsExact (fun literal => eval literal a) formula
  exact congrArg Finset.card setsEqual

end Integration.OpenAIMath.ListFinsetCNFTransport
