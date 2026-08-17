import Mathlib

namespace MathlibPlus.Open.FormalizationBatch.R0109Claim18017

private def psdOperatorLE {𝕜 H : Type*} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    (A B : H →L[𝕜] H) : Prop :=
  ∀ x : H,
    RCLike.re (inner 𝕜 x (A x)) ≤ RCLike.re (inner 𝕜 x (B x))

private def positiveOnSubspace {𝕜 H : Type*} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    (L : Submodule 𝕜 H) (A : H →L[𝕜] H) : Prop :=
  ∀ x : L, 0 ≤ RCLike.re (inner 𝕜 (x : H) (A x))

/-- Claim 18017: for the score transform restricted to the actual subspace
`L` and the complementary orthogonal projections, the Douglas operator order
is exactly positivity of `U*(P₊−P₋)U` on `L`, hence it is also exactly the
contraction-factorization criterion. -/
def claim18017_polarizationPositivityCriterion : Prop :=
  ∀ {𝕜 H K : Type*} [RCLike 𝕜]
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]
    [CompleteSpace H] [CompleteSpace K],
    ∀ (L : Submodule 𝕜 H) [CompleteSpace L]
      (Pplus Pminus : K →L[𝕜] K) (U : H →L[𝕜] K),
      ContinuousLinearMap.adjoint Pplus = Pplus ∧
      ContinuousLinearMap.adjoint Pminus = Pminus ∧
      Pplus.comp Pplus = Pplus ∧
      Pminus.comp Pminus = Pminus ∧
      Pplus.comp Pminus = 0 ∧
      Pminus.comp Pplus = 0 ∧
      Pplus + Pminus = 1 →
        let E : L →L[𝕜] K :=
          Pplus.comp (U.comp L.subtypeL)
        let O : L →L[𝕜] K :=
          Pminus.comp (U.comp L.subtypeL)
        let signed : H →L[𝕜] H :=
          (ContinuousLinearMap.adjoint U).comp
            ((Pplus - Pminus).comp U)
        let order : Prop :=
          psdOperatorLE
            (O.comp (ContinuousLinearMap.adjoint O))
            (E.comp (ContinuousLinearMap.adjoint E))
        let factorization : Prop :=
          ∃ C : L →L[𝕜] L, O = E.comp C ∧ ‖C‖ ≤ 1
        (ContinuousLinearMap.adjoint E).comp E +
              (ContinuousLinearMap.adjoint O).comp O = 1 →
          (factorization ↔ order) ∧
            (order ↔ positiveOnSubspace L signed)

end MathlibPlus.Open.FormalizationBatch.R0109Claim18017
