import AgdaMirror.Base369

/-!
# Lean mirror of `LogicTlurey.agda` (genuine, fully proved)

Faithful transcription of `LogicTlurey.agda`: the four dialectical `Stage`s with
their successor map `next`, the `stageTrace` unfolding, its length, the order-4
periodicity of `next` (`next_fourth`), the `spin`/`next` shift lemma, the trace
periodicity decomposition, and the triadic-tone semantics via `Base369.TriTruth`.
All genuine, proved by structural induction / case analysis.
-/

namespace AgdaMirror.LogicTlurey

open AgdaMirror.Base369

inductive Stage | seed | counter | resonance | overflow
  deriving DecidableEq

def next : Stage → Stage
  | .seed => .counter | .counter => .resonance
  | .resonance => .overflow | .overflow => .seed

def stageTrace : Nat → Stage → List Stage
  | 0, _ => []
  | n + 1, s => s :: stageTrace n (next s)

theorem stageTrace_length (n : Nat) (s : Stage) : (stageTrace n s).length = n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simp [stageTrace, ih]

theorem next_fourth (s : Stage) : spin 4 next s = s := by cases s <;> rfl

theorem spin_next_succ (n : Nat) (s : Stage) :
    spin n next (next s) = spin (n + 1) next s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simp only [spin, ih]

theorem stageTrace_periodic (n : Nat) (s : Stage) :
    stageTrace (n + 4) s = stageTrace n s ++ stageTrace 4 (spin n next s) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    show s :: stageTrace (n + 4) (next s) = (s :: stageTrace n (next s)) ++ _
    rw [ih (next s), spin_next_succ]
    rfl

theorem stageTrace_cycle (n : Nat) :
    stageTrace (n + 4) .seed = stageTrace n .seed ++ stageTrace 4 (spin n next .seed) :=
  stageTrace_periodic n .seed

/-- Triadic-tone semantics. -/
def stageTone : Stage → TriTruth
  | .seed => .low | .counter => .mid | .resonance => .high | .overflow => .low

def combineStage (a b : Stage) : TriTruth := triXor (stageTone a) (stageTone b)

theorem stageTone_next_seed :
    stageTone (next .seed) = rotateTri (stageTone .seed) := rfl
theorem stageTone_next_counter :
    stageTone (next .counter) = rotateTri (stageTone .counter) := rfl
theorem stageTone_next_resonance :
    stageTone (next .resonance) = rotateTri (stageTone .resonance) := rfl
theorem stageTone_next_overflow :
    stageTone (next .overflow) = stageTone .seed := rfl

theorem resonance_combine : combineStage .resonance .resonance = .mid := rfl

end AgdaMirror.LogicTlurey
