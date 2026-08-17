import MathlibPlus.Open.ResearchFormalization.R0867PackingDegree

namespace MathlibPlus.Open.ResearchFormalization.R0867HomogeneousDecomposition

noncomputable section

open MathlibPlus.Open.ResearchFormalization.R0867PackingDegree

/-- The homogeneous common-context factor rectangle of the translated
cross-ratio differences. -/
def homogeneousFactorRectangle {σ : Type*} [DecidableEq σ]
    (K : Fin 4 → Form σ) (lam : ℚ) (h : ℕ) : Prop :=
  ∃ H X Y : Form σ, ∃ d r : ℕ,
    H ≠ 0 ∧
    MvPolynomial.IsHomogeneous H d ∧
    MvPolynomial.IsHomogeneous X r ∧
    MvPolynomial.IsHomogeneous Y r ∧
    IsCoprime X Y ∧
    IsCoprime (scalarForm lam * X - Y) X ∧
    IsCoprime (scalarForm lam * X - Y) Y ∧
    centeredA K = H * X * (scalarForm lam * X - Y) ∧
    centeredB K = H * Y * (scalarForm lam * X - Y) ∧
    centeredD K = scalarForm (lam - 1) * H * X * Y ∧
    h = d + 2 * r

/-- Claim 25475: under the all-distinct homogeneous cross-ratio setup, the
translated differences admit a homogeneous primitive binary factor rectangle,
and the common degree splits as `deg H + 2 * r`. -/
def claim25475 : Prop :=
  ∀ {σ : Type*} [DecidableEq σ]
    (K : Fin 4 → Form σ) (lam : ℚ) (h : ℕ),
    homogeneousAllDistinctCrossRatio K lam h →
      homogeneousFactorRectangle K lam h

end
end MathlibPlus.Open.ResearchFormalization.R0867HomogeneousDecomposition
