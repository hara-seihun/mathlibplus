import MathlibPlus.Open.ResearchFormalization.R0867PackingDegree

namespace MathlibPlus.Open.CrossRatioCore

open MathlibPlus.Open.ResearchFormalization.R0867PackingDegree

noncomputable section

/-- The homogeneous common-context factorization attached to the centered
cross-ratio differences. -/
def homogeneousCoreFactorization {σ : Type*} [DecidableEq σ]
    (K : Fin 4 → Form σ) (lam : ℚ) (h : ℕ)
    (H X Y : Form σ) (r : ℕ) : Prop :=
  H ≠ 0 ∧
    MvPolynomial.IsHomogeneous H (h - 2 * r) ∧
    MvPolynomial.IsHomogeneous X r ∧
    MvPolynomial.IsHomogeneous Y r ∧
    IsCoprime X Y ∧
    IsCoprime (scalarForm lam * X - Y) X ∧
    IsCoprime (scalarForm lam * X - Y) Y ∧
    centeredA K = H * (scalarForm lam * X - Y) * X ∧
    centeredB K = H * (scalarForm lam * X - Y) * Y ∧
    centeredD K = scalarForm (lam - 1) * H * X * Y ∧
    h = (h - 2 * r) + 2 * r

/-- Claim 25477: a non-affine-line homogeneous all-distinct cross-ratio
solution has a positive primitive degree and a common context losing at least
 two degrees, with the factorization tied to the original four forms. -/
def claim25477_nonconstantCoreLosesTwoDegrees : Prop :=
  ∀ {σ : Type*} [DecidableEq σ]
    (K : Fin 4 → Form σ) (lam : ℚ) (h : ℕ),
    homogeneousAllDistinctCrossRatio K lam h →
      ¬ affineFormLine K →
        ∃ (H X Y : Form σ) (r : ℕ),
          1 ≤ r ∧
          h - 2 * r ≤ h - 2 ∧
          homogeneousCoreFactorization K lam h H X Y r

end
end MathlibPlus.Open.CrossRatioCore
