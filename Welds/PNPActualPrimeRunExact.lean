import Welds.PNPActualPrimeLayoutExact

namespace PNPActualPrimeRun
open scoped BigOperators
open PNPStackEmittedList PNPActualPrimeLayout PNPPrimeValuationPriority

abbrev E := PNPStackEmittedList.Edge

theorem valuation_add (Q A : Nat) (u v : Lane Q A → Nat) :
    valuation Q A (u+v) = valuation Q A u + valuation Q A v := by
  classical
  simp [valuation,Finsupp.single_add,Finset.sum_add_distrib]

def residualVector (Q A : Nat) (r : E) (s : State) : Lane Q A → Nat
  | .inl i => s.data i-r.body.take i
  | .inr _ => 0

def successor (r : E) (s : State) : State :=
  ⟨r.body.dst,fun i => s.data i-r.body.take i+r.body.give i⟩

theorem sourceSplit (Q A : Nat) (r : E) (s : State) (en : enabled r s) :
    vector Q A s.data s.tag =
      vector Q A r.body.take r.src + residualVector Q A r s := by
  funext i
  cases i with
  | inl i =>
    simp [vector,residualVector]
    omega
  | inr i => simp [vector,residualVector,en.1]

theorem destSplit (Q A : Nat) (r : E) (s : State) :
    vector Q A (successor r s).data (successor r s).tag =
      vector Q A r.body.give r.body.dst + residualVector Q A r s := by
  funext i
  cases i with
  | inl i => simp [vector,residualVector,successor,Nat.add_comm]
  | inr i => simp [vector,residualVector,successor]

theorem integer_successor (Q A : Nat) (r : E) (s : State) (en : enabled r s) :
    pack (fractionEdge Q A r).take * integerState Q A (successor r s) =
      integerState Q A s * pack (fractionEdge Q A r).give := by
  let rem := valuation Q A (residualVector Q A r s)
  have hr : PrimeSupported rem := valuation_prime Q A _
  have hs : integerState Q A s = pack ((fractionEdge Q A r).take+rem) := by
    unfold integerState
    rw [sourceSplit Q A r s en,valuation_add]
    rfl
  have hd : integerState Q A (successor r s) = pack ((fractionEdge Q A r).give+rem) := by
    unfold integerState
    rw [destSplit,valuation_add]
    rfl
  rw [hs,hd]
  exact transition_product _ _ rem (fractionEdge Q A r).takePrime
    (fractionEdge Q A r).givePrime hr

theorem first_spec (P : List E) (s : State) (r : E)
    (h : first P s = some r) : r ∈ P ∧ enabled r s := by
  induction P with
  | nil => simp [first] at h
  | cons e es ih =>
    by_cases he : enabled e s
    · simp [first,he] at h
      subst r
      exact ⟨by simp,he⟩
    · have h' : first es s = some r := by simpa [first,he] using h
      obtain ⟨hm,en⟩ := ih h'
      exact ⟨by simp [hm],en⟩

noncomputable def integerStep (Q A : Nat) (P : List E) (n : Nat) : Option Nat :=
  (firstLiteral n (P.map (fractionEdge Q A))).map fun e =>
    (n / pack e.take) * pack e.give

theorem integerStepExact (Q A : Nat) (P : List E) (s : State)
    (layout : ∀ r ∈ P, r.src ∈ inventory Q A) :
    integerStep Q A P (integerState Q A s) =
      (step P s).map (integerState Q A) := by
  unfold integerStep
  rw [← first_literal Q A P s layout]
  cases h : first P s with
  | none => simp [step,h]
  | some r =>
    obtain ⟨mem,en⟩ := first_spec P s r h
    have dvd := (literal_guard Q A r s (layout r mem)).mp en
    have prod := integer_successor Q A r s en
    have nz := pack_nonzero _ (fractionEdge Q A r).takePrime
    have q : integerState Q A s / pack (fractionEdge Q A r).take *
        pack (fractionEdge Q A r).give = integerState Q A (successor r s) := by
      apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero nz)
      calc
        pack (fractionEdge Q A r).take *
            (integerState Q A s / pack (fractionEdge Q A r).take *
             pack (fractionEdge Q A r).give)
            = integerState Q A s * pack (fractionEdge Q A r).give := by
                rw [← Nat.mul_assoc,Nat.mul_div_cancel' dvd]
        _ = _ := prod.symm
    simpa [h,step,successor] using congrArg some q

noncomputable def integerRun (Q A : Nat) (P : List E) : Nat → Nat → Option Nat
  | 0,n => some n
  | k+1,n => (integerStep Q A P n).bind (integerRun Q A P k)

theorem primeRunExact (Q A : Nat) (P : List E)
    (layout : ∀ r ∈ P,r.src ∈ inventory Q A) (k : Nat) (s : State) :
    integerRun Q A P k (integerState Q A s) =
      (PNPActualInstructionLedger.run P k s).map (integerState Q A) := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
    simp only [integerRun,PNPActualInstructionLedger.run,integerStepExact Q A P s layout]
    cases h : step P s with
    | none => rfl
    | some t => simpa [h] using ih t

-- A compiled source membership proof discharges the premise for every
-- emitted edge, with no arbitrary list supplied by the caller.
theorem emit_source_mem (body : Tag → List Body) (ps : List Tag) (r : E)
    (h : r ∈ emit body ps) : r.src ∈ ps := by
  induction ps with
  | nil => simp [emit] at h
  | cons p ps ih =>
    simp only [emit,List.mem_append] at h
    rcases h with h|h
    · obtain ⟨b,_,e⟩ := List.mem_map.mp h
      subst r
      simp
    · exact List.mem_cons_of_mem _ (ih h)

theorem compiled_source_mem (Q A : Nat) (table : Nat → Nat → Option Instruction)
    (r : E) (h : r ∈ compile Q A table) : r.src ∈ inventory Q A :=
  emit_source_mem _ _ _ h

theorem compiled_primeRunExact (Q A : Nat) (table : Nat → Nat → Option Instruction)
    (k : Nat) (s : State) :
    integerRun Q A (compile Q A table) k (integerState Q A s) =
      (PNPActualInstructionLedger.run (compile Q A table) k s).map (integerState Q A) :=
  primeRunExact Q A _ (compiled_source_mem Q A table) k s

-- This is a displayed-guard integer run. Ordinary reduced FRACTRAN
-- agrees when source/destination tags are distinct and take/give lane
-- supports are disjoint. Distinct prime labels alone do not imply that.
def ReducedLayout (Q A : Nat) (r : E) : Prop :=
  r.src ∈ inventory Q A ∧ r.body.dst ∈ inventory Q A ∧ r.src ≠ r.body.dst ∧
    ∀ i, r.body.take i = 0 ∨ r.body.give i = 0

def Separated (r : E) : Prop :=
  r.src ≠ r.body.dst ∧ ∀ i, r.body.take i = 0 ∨ r.body.give i = 0

theorem vector_disjoint (Q A : Nat) (r : E) (h : Separated r)
    (i : Lane Q A) :
    vector Q A r.body.take r.src i = 0 ∨
      vector Q A r.body.give r.body.dst i = 0 := by
  cases i with
  | inl i => exact h.2 i
  | inr i =>
    by_cases e : i.val = r.src
    · right
      simp [vector,e,h.1]
    · left
      simp [vector,e]

-- Exact support disjointness transports through the injective allocation.
theorem valuation_disjoint (Q A : Nat) (r : E) (h : Separated r)
    (p : Nat) :
    (fractionEdge Q A r).take p = 0 ∨ (fractionEdge Q A r).give p = 0 := by
  classical
  by_cases hp : ∃ i : Lane Q A, lanePrime Q A i = p
  · obtain ⟨i,rfl⟩ := hp
    simpa [fractionEdge,valuation_at] using vector_disjoint Q A r h i
  · left
    change valuation Q A (vector Q A r.body.take r.src) p = 0
    simp only [valuation,Finsupp.sum_apply]
    apply Finset.sum_eq_zero
    intro i _
    have ne : lanePrime Q A i ≠ p := fun e => hp ⟨i,e⟩
    simp [Finsupp.single_apply,ne,Ne.symm ne]

theorem separated_coprime (Q A : Nat) (r : E) (h : Separated r) :
    Nat.Coprime (pack (fractionEdge Q A r).take) (pack (fractionEdge Q A r).give) := by
  let a := (fractionEdge Q A r).take
  let b := (fractionEdge Q A r).give
  have ha := pack_nonzero a (fractionEdge Q A r).takePrime
  have hb := pack_nonzero b (fractionEdge Q A r).givePrime
  change Nat.gcd (pack a) (pack b) = 1
  by_contra hn
  obtain ⟨p,prime,div⟩ := Nat.exists_prime_and_dvd hn
  let v : Valuation := Finsupp.single p 1
  have hv : PrimeSupported v := by
    intro q hq
    have eq : q=p := by simpa [v] using hq
    simpa [eq] using prime
  have vp : pack v = p := by simp [pack,v]
  have da : pack v ∣ pack a := by rw [vp]; exact div.trans (Nat.gcd_dvd_left _ _)
  have db : pack v ∣ pack b := by rw [vp]; exact div.trans (Nat.gcd_dvd_right _ _)
  have la := ((guard_iff_dvd v a hv (fractionEdge Q A r).takePrime).mpr da) p
  have lb := ((guard_iff_dvd v b hv (fractionEdge Q A r).givePrime).mpr db) p
  have dis := valuation_disjoint Q A r h p
  simp [v] at la lb
  change a p = 0 ∨ b p = 0 at dis
  omega

theorem reduced_coprime (Q A : Nat) (r : E) (h : ReducedLayout Q A r) :
    Nat.Coprime (pack (fractionEdge Q A r).take) (pack (fractionEdge Q A r).give) :=
  separated_coprime Q A r h.2.2

-- Actual compiler-wide ReducedLayout proof remains: emitted exits and
-- private phases plus table target bounds. This theorem does not claim
-- an Agda-to-Lean kernel-level parser correspondence.
-- The actual normalized split-list source move and the complete prime
-- integer run use the same raw edge count. No extra successor hypothesis.
theorem primeMacroExact (Q A q : Nat) (table : Nat → Nat → Option Instruction)
    (c : PNPStackFractran.Config) (hA : 0<A) (hq : q<Q) (ha : c.scanned<A)
    (hl : ∀ d ∈ c.left,d<A)
    (htarget : ∀ i, table q c.scanned=some i → i.target<Q) :
    ∃ n, integerRun Q A (compile Q A table) n
      (integerState Q A ⟨mainTag (.q q),PNPActualWordBisim.dataOf (max 2 A) c⟩) =
      some (integerState Q A (PNPActualWordBisim.sourceResult (max 2 A) q table c)) := by
  obtain ⟨n,h⟩ := PNPActualWordBisim.raw_step_bisim Q A q table c hA hq ha hl htarget
  refine ⟨n,?_⟩
  rw [compiled_primeRunExact,h]
  rfl

-- Finite checker for concrete compiled tables; proof of its success for
-- ALL legal tables is distinct from the decidable concrete receipt.
def layoutCheck (Q A : Nat) (r : E) : Bool :=
  decide (r.src ∈ inventory Q A) &&
  decide (r.body.dst ∈ inventory Q A) &&
  decide (r.src ≠ r.body.dst) &&
  decide (∀ i : Fin 5, r.body.take i = 0 ∨ r.body.give i = 0)

theorem layoutCheck_sound (Q A : Nat) (r : E)
    (h : layoutCheck Q A r = true) : ReducedLayout Q A r := by
  simpa [layoutCheck,ReducedLayout,Bool.and_eq_true, and_assoc] using h

def programLayoutCheck (Q A : Nat) (table : Nat → Nat → Option Instruction) : Bool :=
  (compile Q A table).all (layoutCheck Q A)

theorem compiled_reduced_receipt (Q A : Nat) (table : Nat → Nat → Option Instruction)
    (ok : programLayoutCheck Q A table = true) (r : E)
    (mem : r ∈ compile Q A table) :
    Nat.Coprime (pack (fractionEdge Q A r).take) (pack (fractionEdge Q A r).give) := by
  exact reduced_coprime Q A r (layoutCheck_sound Q A r ((List.all_eq_true.mp ok) r mem))

end PNPActualPrimeRun
