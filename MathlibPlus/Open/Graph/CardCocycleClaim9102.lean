import Mathlib
import MathlibPlus.Open.FormalizationBatch

namespace MathlibPlus.Open.CardCocycle

open MathlibPlus.Open.FormalizationBatch

noncomputable def globallyIsomorphic
    {V : Type*} [DecidableEq V]
    (A B : SimpleLabeledGraph V) : Prop :=
  ∃ σ : Equiv.Perm V, ∀ e : Edge V, A e = B (edgeImage σ e)

/-- A component coloring may change labeled edge bits without producing a
nonisomorphic pair: the two projected simple labeled graphs can still be
related by one global vertex permutation. -/
def labeledInequalityIsNotACounterexampleCertificate : Prop :=
  ∃ (V : Type*) (_ : Fintype V) (_ : DecidableEq V),
    ∃ π : PointedLocalPermutations V,
      ∃ c : GammaVertex V → Bool,
        IsGammaComponentColoring π c ∧
          RealizesPrescribedCardIsomorphisms π
            (componentColoringProjection π c).1
            (componentColoringProjection π c).2 ∧
          (∃ e : Edge V,
            (componentColoringProjection π c).1 e ≠
              (componentColoringProjection π c).2 e) ∧
          globallyIsomorphic
            (componentColoringProjection π c).1
            (componentColoringProjection π c).2

end MathlibPlus.Open.CardCocycle
