import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0106Claim17998

noncomputable section

/-- Claim 17998: in finite-dimensional real inner-product spaces, the adjoint
of a linear isometry is a left inverse, and every finite linear trace preserves
that operator equality. -/
def claim17998 : Prop :=
  ∀ {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]
    (𝔇ₑ : V →ₗᵢ[ℝ] W),
    let coisometry : (V →L[ℝ] V) :=
      (ContinuousLinearMap.adjoint 𝔇ₑ.toContinuousLinearMap).comp
        𝔇ₑ.toContinuousLinearMap
    coisometry = ContinuousLinearMap.id ℝ V ∧
      ∀ {R : Type*} [AddCommGroup R] [Module ℝ R]
        (τ : (V →L[ℝ] V) →ₗ[ℝ] R),
        τ coisometry = τ (ContinuousLinearMap.id ℝ V)

end
end MathlibPlus.Open.ResearchFormalization.R0106Claim17998
