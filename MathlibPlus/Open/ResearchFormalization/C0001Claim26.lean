import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.C0001Claim26

/-- The determinant/correlation identity and its cumulative-increment square-root
form, with the nonzero and nonnegative hypotheses needed by the displayed
fractions and square-root branch. -/
def correlationIncrementFraction_claim26 : Prop :=
  (∀ (D L R I C rho chi chiPrev delta : ℝ),
    D ≠ 0 →
    L ≠ 0 →
    R ≠ 0 →
    rho ^ 2 = C ^ 2 / (L * R) →
    chi = R / D →
    chiPrev = I / L →
    delta = chi - chiPrev →
    D * I = L * R - C ^ 2 →
    rho ^ 2 = delta / chi) ∧
  (∀ (increment chi rho : ℕ → ℝ),
    (∀ n, chi n = ∑ k ∈ Finset.range (n + 1), increment k) →
    (∀ n, 0 ≤ rho n) →
    (∀ n, rho n ^ 2 = increment n / chi n) →
    ∀ n,
      rho n = Real.sqrt
        (increment n /
          (∑ k ∈ Finset.range (n + 1), increment k)))

end MathlibPlus.Open.ResearchFormalization.C0001Claim26
