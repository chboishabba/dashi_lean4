import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.TLiftK

/-!
# Original TLiftK: selected CM/Hecke fibre witness extraction.

This is a source-exact ORIGINAL operator/field/weight type, not a finite
C3 reinterpretation. Its producer is the fork's already-defined
`UpperTheory.TP.K.tLiftK`. The result exposes the real remainder obligation:
a threshold d₀ and, for d≥d₀, an actual automorphic target U' with
`IsLift B χX χW mX mW lam U U'`.

This proof imports the original theta theorem directly. It does not prove
the underlying TLiftK, shorten its dependency closure or show that our
zero/zeta/zeta² indexed C3 phase carrier is a Hecke character.
DASHI phase/sign/residual transport must attach to a *selected instance* of
this telescope, using this actual IsLift contract.
Source-written, Lean 4.33.1 kernel check pending, no CI.
-/

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
  GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.PRep
  Formalism.BasicNotions

namespace DASHI.AlpogeRH.SelectedTheta

/-- The original theorem instantiated only through the chosen source
CM base, Hermitian input and GoodK premises. All later quantified Hecke
and automorphic hypotheses are retained literally. -/
theorem actual_selected_fibre_of_original_TLiftK
    (E : Type) [Field E] [NumberField E] [IsCMField E]
    (B : Base (maximalRealSubfield E) E)
    (hgood : W.GoodK (cj E) B)
    (n : ℕ) (hn : 1 ≤ n)
    (X : Spc (maximalRealSubfield E) E n)
    (hJ : X.J = 1)
    (hHerm : X.IsHerm (cj E) B n 0) :
    ∃ d₀ : ℕ, ∀ d, d₀ ≤ d →
      ∀ (W : Spc (maximalRealSubfield E) E d) (δ : E),
        W.J = δ • (1 : Matrix (Fin d) (Fin d) E) →
        W.IsSkew (cj E) B d 0 →
        ∀ (χX χW : Chr (maximalRealSubfield E) E)
          (mX mW : InfinitePlace (maximalRealSubfield E) → ℤ),
          IsHecke (maximalRealSubfield E) E χX →
          IsHecke (maximalRealSubfield E) E χW →
          ResEtaPow
            (Units.map
              (algebraMap (maximalRealSubfield E)
                (AF (maximalRealSubfield E))).toMonoidHom).range χX n →
          ResEtaPow
            (Units.map
              (algebraMap (maximalRealSubfield E)
                (AF (maximalRealSubfield E))).toMonoidHom).range χW d →
          HasExp B.emb χX mX →
          HasExp B.emb χW mW →
          ∀ (U : Submodule ℂ (GlobalTheory.UnitaryBC.UA E n → ℂ))
            (lam : InfinitePlace (maximalRealSubfield E) → DomWeight n),
            GlobalTheory.UnitaryBC.IsAutRepU U →
            (∀ w, GlobalTheory.UnitaryBC.HasWeightAt U (B.emb w).1 (lam w)) →
            (∀ w k, (d : ℤ) + mW w ≤ 2 * (lam w).w k) →
            ∃ U' : Submodule ℂ (GlobalTheory.UnitaryBC.UA E d → ℂ),
              IsLift B χX χW mX mW lam U U' := by
  exact UpperTheory.TP.K.tLiftK E B hgood n hn X hJ hHerm

#print axioms actual_selected_fibre_of_original_TLiftK

end DASHI.AlpogeRH.SelectedTheta
