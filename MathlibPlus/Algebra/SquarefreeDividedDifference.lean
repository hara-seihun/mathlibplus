import Mathlib

namespace MathlibPlus.Algebra.SquarefreeDividedDifference

/-- Claim 22403: the two distinct-root squarefree interpolation trade has the
constant result `1`, so it is a nontrivial constant trade rather than a
repeated-root divisibility relation. -/
def squarefreeSyntheticTrade_claim22403 : Prop :=
  ∀ {K : Type*} [Field K]
    (kappa₁ kappa₂ Y : K),
    kappa₁ ≠ kappa₂ →
      (Y + kappa₂) / (kappa₂ - kappa₁) -
          (Y + kappa₁) / (kappa₂ - kappa₁) = (1 : K)

end MathlibPlus.Algebra.SquarefreeDividedDifference
