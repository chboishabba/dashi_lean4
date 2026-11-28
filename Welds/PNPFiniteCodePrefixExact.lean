import Welds.PNPFixedSourceGainExact

namespace PNPFiniteCodePrefix
open PNPFixedSourceGain

-- Fixed finite source list, actual syntax, actual verified output.
-- Compile once by finite search; the resulting code may hardwire the
-- table. Offline construction is not charged as runtime of that code.
def firstWitness {n : Nat} (F : CNF n) : List (Assignment n) → Option (Assignment n)
  | [] => none
  | x::xs => if eval F x then some x else firstWitness F xs

theorem firstWitness_sound {n : Nat} (F : CNF n) (xs : List (Assignment n))
    (x : Assignment n) (h : firstWitness F xs=some x) : Sat F x := by
  induction xs with
  | nil => simp [firstWitness] at h
  | cons y ys ih =>
    by_cases hy : eval F y=true
    · have e : y=x := by simpa [firstWitness,hy] using h
      subst y
      exact (eval_exact F x).1 hy
    · exact ih (by simpa [firstWitness,hy] using h)

theorem firstWitness_complete {n : Nat} (F : CNF n) (xs : List (Assignment n))
    (x : Assignment n) (hx : x∈xs) (hs : Sat F x) :
    ∃ y, firstWitness F xs=some y := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
    by_cases hy : eval F y=true
    · exact ⟨y,by simp [firstWitness,hy]⟩
    · rcases List.mem_cons.mp hx with e|e
      · subst y
        exact False.elim (hy ((eval_exact F x).2 hs))
      · obtain ⟨z,hz⟩ := ih e
        exact ⟨z,by simpa [firstWitness,hy] using hz⟩

abbrev Entry (n : Nat) := CNF n × Option (Assignment n)

def compile {n : Nat} (xs : List (Assignment n)) (sources : List (CNF n)) :
    List (Entry n) := sources.map (fun F => (F,firstWitness F xs))

def lookup {n : Nat} (F : CNF n) : List (Entry n) → Option (Assignment n)
  | [] => none
  | (G,x)::es => if G=F then x else lookup F es

theorem lookup_compiled {n : Nat} (xs : List (Assignment n)) (sources : List (CNF n))
    (F : CNF n) (h : F∈sources) :
    lookup F (compile xs sources)=firstWitness F xs := by
  induction sources with
  | nil => simp at h
  | cons G Gs ih =>
    by_cases he : G=F
    · subst G
      simp [compile,lookup]
    · have hm : F∈Gs := by
        rcases List.mem_cons.mp h with h|h
        · exact False.elim (he h.symm)
        · exact h
      simpa [compile,lookup,he] using ih hm

theorem run_preserves_raw_success {n : Nat} (raw : CNF n → Option (Assignment n))
    (F : CNF n) (x : Assignment n) (h : raw F=some x) (hs : Sat F x) :
    score raw F=true := by
  have hv := (eval_exact F x).2 hs
  unfold score run
  split <;> simp [h,hv]

theorem finite_prefix_complete {n : Nat} (xs : List (Assignment n))
    (all : ∀ x : Assignment n,x∈xs) (sources : List (CNF n))
    (F : CNF n) (hf : F∈sources) (x : Assignment n) (hs : Sat F x) :
    score (fun G => lookup G (compile xs sources)) F=true := by
  obtain ⟨y,hy⟩ := firstWitness_complete F xs x (all x) hs
  apply run_preserves_raw_success _ F y
  · rw [lookup_compiled xs sources F hf]
    exact hy
  · exact firstWitness_sound F xs y hy

theorem child_success_parent_sat {n : Nat} (raw : CNF n → Option (Assignment n))
    (F : CNF n) (l : Literal n) (h : score raw (F++[[l]])=true) :
    ∃ x, Sat F x := by
  cases he : run raw (F++[[l]]) with
  | none => simp [score,he] at h
  | some x =>
    have hx := run_sound raw (F++[[l]]) x he
    exact ⟨x,fun c hc => hx c (List.mem_append.mpr (Or.inl hc))⟩

theorem no_gain_on_complete_prefix {n : Nat} (raw : CNF n → Option (Assignment n))
    (sources : List (CNF n))
    (complete : ∀ F∈sources, ∀ x, Sat F x → score raw F=true)
    (F : CNF n) (hF : F∈sources) (l : Literal n) :
    ¬ (score raw F=false ∧ score raw (F++[[l]])=true) := by
  rintro ⟨h0,h1⟩
  obtain ⟨x,hx⟩ := child_success_parent_sat raw F l h1
  rw [complete F hF x hx] at h0
  simp at h0

theorem compiled_prefix_no_gain {n : Nat} (xs : List (Assignment n))
    (all : ∀ x : Assignment n,x∈xs) (sources : List (CNF n))
    (F : CNF n) (hF : F∈sources) (l : Literal n) :
    let raw := fun G => lookup G (compile xs sources)
    ¬ (score raw F=false ∧ score raw (F++[[l]])=true) :=
  no_gain_on_complete_prefix _ sources
    (fun G hG x hx => finite_prefix_complete xs all sources G hG x hx) F hF l

-- A finite exhaustive source prefix can always be hardwired into the
-- full code. This does NOT supply a computable deadline depending on
-- that full code. The actual finite-state trie realization is tested
-- separately; this native list lookup has no asserted linear clock.
end PNPFiniteCodePrefix
