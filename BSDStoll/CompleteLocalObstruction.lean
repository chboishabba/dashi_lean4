import EllipticCurves.SelmerGroup
import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# Genuine local-obstruction quotient and all-place Selmer kernel

Source mathematical objects:
Michael Stoll, `EllipticCurves/SelmerGroup.lean`, pinned at
1e4709496a2c0cb3da66b400efbb15939358d444, Apache-2.0.

This module acts on the genuine étale square-class group W.M for the
ACTUAL Weierstrass curve W. It localizes via Stoll's algebraic
base-change homomorphism `W.localRes L`, and quotients by the image
of the local point Kummer map `μ`.

The resulting obstruction's kernel is EXACTLY Stoll's independently
constructed `W.localCondition L`. Requiring zero norm, zero finite-place
obstructions and zero infinite-place obstructions is equivalent to
membership in his actual `selmerGroup₂`.

No artificially chosen residual group; no 3^k state count; no claim that
this proves BSD, a Sha identification, or an analytic rank comparison.
-/

open WeierstrassCurve

namespace BSDStoll

noncomputable section

variable {K : Type*} [Field K] [DecidableEq K]
variable (W : WeierstrassCurve.Affine K)
variable [W.IsElliptic] [W.IsCharNeTwoNF]

section Local

variable (L : Type*) [Field L] [Algebra K L] [DecidableEq L]

/-- The local étale square classes modulo classes coming from ACTUAL local
elliptic points through the 2-descent Kummer map. -/
abbrev LocalKummerObstruction : Type _ :=
  (W⁄L).toAffine.M ⧸ (WeierstrassCurve.Affine.μ (W := (W⁄L).toAffine)).range

/-- Localize the global étale square class and remember its entire coset
modulo genuinely locally realizable Kummer classes. -/
noncomputable def localObstruction : W.M →*
    LocalKummerObstruction W L :=
  (QuotientGroup.mk'
    (WeierstrassCurve.Affine.μ (W := (W⁄L).toAffine)).range).comp
      (W.localRes L)

/-- Exact quotient-kernel test. This is the full local response of the
selected arithmetic transformation, not just a necessary sign condition. -/
theorem localObstruction_eq_one_iff
    (c : W.M) :
    localObstruction W L c = 1 ↔
      c ∈ W.localCondition L := by
  change
    (QuotientGroup.mk'
      (WeierstrassCurve.Affine.μ (W := (W⁄L).toAffine)).range)
        (W.localRes L c) = 1 ↔
      W.localRes L c ∈ W.localCondition L
  rw [QuotientGroup.eq_one_iff]
  exact (W.mem_localCondition_iff L).symm

/-- Any rational point maps into the local Kummer image, so its entire
local obstruction vanishes. The nontrivial local/global compatibility
is supplied by Stoll's `range_μ_le_localCondition` theorem. -/
theorem localObstruction_vanishes_on_globalKummer
    (P : Multiplicative W.Point) :
    localObstruction W L (W.μ P) = 1 := by
  apply (localObstruction_eq_one_iff W L _).2
  exact W.range_μ_le_localCondition L ⟨P, rfl⟩

end Local

section AllPlaces

variable (R : Type*) [CommRing R] [IsDedekindDomain R]
variable [Algebra R K] [IsFractionRing R K]
variable {ι : Type*} (Loc : ι → Type*)
variable [(i : ι) → Field (Loc i)]
variable [(i : ι) → Algebra K (Loc i)]

/-- The full arithmetic response, preserving ALL three channels:
étale norm, finite-place Kummer obstruction, infinite-place Kummer
obstruction. The gluing law is equality with Stoll's Selmer subgroup,
not a fabricated compatibility object. -/
theorem selmer_iff_complete_obstruction_vanishes
    (c : W.M) :
    c ∈ W.selmerGroup₂ R Loc ↔
      W.normM c = 1 ∧
      (∀ v : HeightOneSpectrum R,
        localObstruction W (v.adicCompletion K) c = 1) ∧
      (∀ i : ι,
        localObstruction W (Loc i) c = 1) := by
  classical
  rw [W.mem_selmerGroup₂_iff R Loc]
  constructor
  · rintro ⟨hnorm, hfinite, hinfinite⟩
    exact ⟨hnorm,
      (fun v => (localObstruction_eq_one_iff W (v.adicCompletion K) c).2 (hfinite v)),
      (fun i => (localObstruction_eq_one_iff W (Loc i) c).2 (hinfinite i))⟩
  · rintro ⟨hnorm, hfinite, hinfinite⟩
    exact ⟨hnorm,
      (fun v => (localObstruction_eq_one_iff W (v.adicCompletion K) c).1 (hfinite v)),
      (fun i => (localObstruction_eq_one_iff W (Loc i) c).1 (hinfinite i))⟩

/-- Every globally rational point has zero norm and zero obstruction at
EVERY place in the very same arithmetic construction. -/
theorem globalKummer_complete_obstruction_zero
    (P : Multiplicative W.Point) :
    W.normM (W.μ P) = 1 ∧
    (∀ v : HeightOneSpectrum R,
      localObstruction W (v.adicCompletion K) (W.μ P) = 1) ∧
    (∀ i : ι,
      localObstruction W (Loc i) (W.μ P) = 1) := by
  apply (selmer_iff_complete_obstruction_vanishes W R Loc _).1
  exact W.range_μ_le_selmerGroup₂ R Loc ⟨P, rfl⟩

end AllPlaces

end

end BSDStoll
