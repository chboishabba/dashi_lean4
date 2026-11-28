import Welds.PNPPuncturedSupportGainBisectionExact

namespace PNPFixedSourceGain

-- Syntax-sensitive ordered original CNF. Do not normalize a machine's
-- actual input when searching for a counterexample.
abbrev Literal (n : Nat) := Fin n × Bool
abbrev CNF (n : Nat) := List (List (Literal n))
abbrev Assignment (n : Nat) := Fin n → Bool

def evalClause {n : Nat} (x : Assignment n) (c : List (Literal n)) : Bool :=
  c.any (fun p => decide (x p.1=p.2))

def eval {n : Nat} (F : CNF n) (x : Assignment n) : Bool :=
  F.all (evalClause x)

def Sat {n : Nat} (F : CNF n) (x : Assignment n) : Prop :=
  ∀ c∈F, ∃ p∈c, x p.1=p.2

theorem eval_exact {n : Nat} (F : CNF n) (x : Assignment n) :
    eval F x=true ↔ Sat F x := by
  simp [eval,evalClause,Sat,List.all_eq_true,List.any_eq_true]

def guess {n : Nat} (F : CNF n) (i : Fin n) : Bool :=
  decide ([(i,true)]∈F)

def ready {n : Nat} (F : CNF n) : Bool :=
  (List.finRange n).all (fun i => decide ([(i,guess F i)]∈F))

def run {n : Nat} (raw : CNF n → Option (Assignment n)) (F : CNF n) :
    Option (Assignment n) :=
  if ready F && eval F (guess F) then some (guess F)
  else
    match raw F with
    | none => none
    | some x => if eval F x then some x else none

theorem run_sound {n : Nat} (raw : CNF n → Option (Assignment n))
    (F : CNF n) (x : Assignment n) (h : run raw F=some x) : Sat F x := by
  unfold run at h
  split at h
  · rename_i hgood
    have e : guess F=x := Option.some.inj h
    subst x
    exact (eval_exact F _).1 (Bool.and_eq_true.mp hgood).2
  · cases hr : raw F with
    | none => simp [hr] at h
    | some y =>
      simp only [hr] at h
      split at h
      · rename_i hy
        have e : y=x := Option.some.inj h
        subst x
        exact (eval_exact F _).1 hy
      · simp at h

theorem anchor_ready {n : Nat} (F : CNF n) (x : Assignment n)
    (h : Sat F x) (pins : ∀ i, [(i,x i)]∈F) : guess F=x := by
  funext i
  cases hx : x i
  · have hn : [(i,true)]∉F := by
      intro hm
      obtain ⟨p,hp,he⟩ := h _ hm
      have ep : p=(i,true) := by simpa using hp
      subst p
      simp [hx] at he
    simp [guess,hn,hx]
  · have hm : [(i,true)]∈F := by simpa [hx] using pins i
    simp [guess,hm,hx]

theorem fullAnchor {n : Nat} (raw : CNF n → Option (Assignment n))
    (F : CNF n) (x : Assignment n) (h : Sat F x)
    (pins : ∀ i, [(i,x i)]∈F) : run raw F=some x := by
  have eg := anchor_ready F x h pins
  have hr : ready F=true := by
    simp only [ready,List.all_eq_true,decide_eq_true_eq]
    intro i hi
    rw [eg]
    exact pins i
  have hv := (eval_exact F x).2 h
  simp [run,hr,eg,hv]

def pinList {n : Nat} (x : Assignment n) : List (Literal n) :=
  (List.finRange n).map (fun i => (i,x i))

def prefix {n : Nat} (F : CNF n) (x : Assignment n) (i : Nat) : CNF n :=
  F ++ ((pinList x).take i).map (fun p => [p])

theorem fullPrefixSat {n : Nat} (F : CNF n) (x : Assignment n)
    (h : Sat F x) : Sat (prefix F x n) x := by
  intro c hc
  have hlen : (pinList x).length=n := by simp [pinList]
  have ht : (pinList x).take n=pinList x := by
    rw [← hlen] at *
    simp
  simp only [prefix,ht,List.mem_append,List.mem_map] at hc
  rcases hc with hc|⟨p,hp,e⟩
  · exact h c hc
  · subst c
    obtain ⟨i,_,hi⟩ := List.mem_map.mp hp
    subst p
    exact ⟨(i,x i),by simp,rfl⟩

theorem fullPrefixPinned {n : Nat} (F : CNF n) (x : Assignment n) (i : Fin n) :
    [(i,x i)]∈prefix F x n := by
  have hlen : (pinList x).length=n := by simp [pinList]
  have ht : (pinList x).take n=pinList x := by
    rw [← hlen]
    simp
  apply List.mem_append.mpr
  right
  rw [ht]
  exact List.mem_map.mpr ⟨(i,x i),List.mem_map.mpr ⟨i,by simp,rfl⟩,rfl⟩

def score {n : Nat} (raw : CNF n → Option (Assignment n)) (F : CNF n) : Bool :=
  (run raw F).isSome

theorem fullPrefixScore {n : Nat} (raw : CNF n → Option (Assignment n))
    (F : CNF n) (x : Assignment n) (h : Sat F x) :
    score raw (prefix F x n)=true := by
  simp [score,fullAnchor raw _ x (fullPrefixSat F x h) (fullPrefixPinned F x)]

theorem take_succ_exists {A : Type*} (xs : List A) (i : Nat) (h : i<xs.length) :
    ∃ a, xs.take (i+1)=xs.take i++[a] := by
  induction xs generalizing i with
  | nil => simp at h
  | cons a xs ih =>
    cases i with
    | zero => exact ⟨a,rfl⟩
    | succ i =>
      obtain ⟨b,hb⟩ := ih i (by simpa using h)
      exact ⟨b,by simp [hb,Nat.succ_eq_add_one]⟩

theorem nextPrefix {n : Nat} (F : CNF n) (x : Assignment n) (i : Nat) (h : i<n) :
    ∃ l : Literal n, prefix F x (i+1)=prefix F x i++[[l]] := by
  obtain ⟨l,hl⟩ := take_succ_exists (pinList x) i (by simpa [pinList] using h)
  exact ⟨l,by simp [prefix,hl,List.map_append,List.append_assoc]⟩

theorem missed_source_gain {n : Nat} (raw : CNF n → Option (Assignment n))
    (F : CNF n) (x : Assignment n) (h : Sat F x)
    (hn : 0<n) (fuel : Nat) (hf : n≤2^fuel)
    (miss : score raw F=false) :
    ∃ G : CNF n, ∃ l : Literal n, score raw G=false ∧ score raw (G++[[l]])=true := by
  have hlo : score raw (prefix F x 0)=false := by simpa [prefix] using miss
  obtain ⟨i,_,_,hi,h0,h1⟩ := PNPGainBisection.search_exact
    (fun j => score raw (prefix F x j)) fuel 0 n hn (by simpa using hf)
    hlo (fullPrefixScore raw F x h)
  obtain ⟨l,hl⟩ := nextPrefix F x i (by omega)
  exact ⟨prefix F x i,l,h0,by rw [← hl]; exact h1⟩

-- This uses one fixed source-defined run at all endpoints. The raw
-- clock and syntax enumeration are separate; no total computable
-- gain deadline for every polynomial code is inferred.
end PNPFixedSourceGain
