import NobelChemistry.AsymmetricAutocatalysis

namespace NobelChemistry

/-- Finite iteration of the amplification step, kept local to this model. -/
def iter : Nat → ChiralBias → ChiralBias
  | 0, x => x
  | n + 1, x => amplify (iter n x)

@[simp] theorem iter_zero (x : ChiralBias) : iter 0 x = x := rfl
@[simp] theorem iter_succ (n : Nat) (x : ChiralBias) : iter (n + 1) x = amplify (iter n x) := rfl

/-- One-step mirror equivariance extends to every finite iterate. -/
theorem iter_mirror_equivariant :
    ∀ n x, iter n (mirror x) = mirror (iter n x) := by
  intro n
  induction n with
  | zero => intro x; rfl
  | succ n ih =>
      intro x
      simp [iter, ih, amplify_mirror_equivariant]

/-- The amplified left branch is stable under every finite iterate. -/
theorem left_branch_stable : ∀ n, iter n ChiralBias.leftAmplified = ChiralBias.leftAmplified := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => simp [iter, ih]

/-- The amplified right branch is stable under every finite iterate. -/
theorem right_branch_stable : ∀ n, iter n ChiralBias.rightAmplified = ChiralBias.rightAmplified := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => simp [iter, ih]

/-- The racemic state remains fixed under every finite iterate. -/
theorem racemic_stable : ∀ n, iter n ChiralBias.racemic = ChiralBias.racemic := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => simp [iter, ih]

/-- Any positive number of amplification steps places the left seed on the stable left branch. -/
theorem left_seed_reaches_branch :
    ∀ n, iter (n + 1) ChiralBias.leftSeed = ChiralBias.leftAmplified := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => simp [iter, ih]

/-- Any positive number of amplification steps places the right seed on the stable right branch. -/
theorem right_seed_reaches_branch :
    ∀ n, iter (n + 1) ChiralBias.rightSeed = ChiralBias.rightAmplified := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => simp [iter, ih]

end NobelChemistry
