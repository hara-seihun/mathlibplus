import Mathlib
import MathlibPlus.Open.ResearchFormalization.R0867PackingDegree

namespace MathlibPlus.Open.ResearchFormalization.R0867ScalarCore

noncomputable section

open MathlibPlus.Open.ResearchFormalization.R0867PackingDegree

/-- The homogeneous common-context factor rectangle from the translated
all-distinct cross-ratio normal form.  The degree `s` is the degree of the
common context and `r` is the common degree of the two primitive directions;
the final equation records the reviewed degree split. -/
def commonContextBinaryFactorRectangle {σ : Type*} [DecidableEq σ]
    (K : Fin 4 → Form σ) (lam : ℚ) (h s r : ℕ)
    (H X Y : Form σ) : Prop :=
  H ≠ 0 ∧
    MvPolynomial.IsHomogeneous H s ∧
    MvPolynomial.IsHomogeneous X r ∧
    MvPolynomial.IsHomogeneous Y r ∧
    IsCoprime X Y ∧
    IsCoprime (scalarForm lam * X - Y) X ∧
    IsCoprime (scalarForm lam * X - Y) Y ∧
    centeredA K = H * (scalarForm lam * X - Y) * X ∧
    centeredB K = H * (scalarForm lam * X - Y) * Y ∧
    centeredD K = scalarForm (lam - 1) * H * X * Y ∧
    h = s + 2 * r

/-- Claim 25476: for the exact all-distinct homogeneous cross-ratio and
common-context factor-rectangle carrier, a scalar core gives the affine-line
case, while failure of the affine-line predicate forces a positive core
degree. -/
def claim25476 : Prop :=
  ∀ (σ : Type*) [DecidableEq σ]
    (K : Fin 4 → Form σ) (lam : ℚ) (h s r : ℕ)
    (H X Y : Form σ),
    homogeneousAllDistinctCrossRatio K lam h →
      commonContextBinaryFactorRectangle K lam h s r H X Y →
        ((r = 0 → affineFormLine K) ∧
          (¬affineFormLine K → 1 ≤ r))

end

end MathlibPlus.Open.ResearchFormalization.R0867ScalarCore
