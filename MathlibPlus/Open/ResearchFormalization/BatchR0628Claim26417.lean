import Mathlib
import MathlibPlus.Open.Research.ScalarAlgebra

namespace MathlibPlus.Open.ResearchFormalization.BatchR0628Claim26417

open MathlibPlus.Open.ResearchFormalizationBatch

/-- Claim 26417: the concrete scalar pullback and ambient polynomial ring have
identified fraction fields, with the nonzero e₂/ze₂ recovery of z and all
ambient generators. -/
def claim26417_scalarPullbackFractionFieldEquality : Prop :=
  ∃ e : FractionRing scalarA ≃ₐ[ℚ] FractionRing ScalarR,
    (∀ a : scalarA,
      e (algebraMap scalarA (FractionRing scalarA) a) =
        algebraMap ScalarR (FractionRing ScalarR) (a : ScalarR)) ∧
    ∃ a₂ az₂ : scalarA,
      (a₂ : ScalarR) = scalarE 0 ∧
      (az₂ : ScalarR) = scalarZ * scalarE 0 ∧
      (scalarE 0 : ScalarR) ≠ 0 ∧
      e.symm (algebraMap ScalarR (FractionRing ScalarR) scalarZ) =
        algebraMap scalarA (FractionRing scalarA) az₂ /
          algebraMap scalarA (FractionRing scalarA) a₂ ∧
      e.symm (algebraMap ScalarR (FractionRing ScalarR) scalarS) =
        algebraMap scalarA (FractionRing scalarA)
          ⟨scalarS, Algebra.subset_adjoin (Set.mem_union_left _ rfl)⟩ ∧
      (∀ k : ℕ,
        e.symm (algebraMap ScalarR (FractionRing ScalarR) (MvPolynomial.X (k + 2))) =
          algebraMap scalarA (FractionRing scalarA)
            ⟨scalarE k, Algebra.subset_adjoin
              (Set.mem_union_right _ (Ideal.subset_span (Set.mem_range_self k)))⟩)

end MathlibPlus.Open.ResearchFormalization.BatchR0628Claim26417
