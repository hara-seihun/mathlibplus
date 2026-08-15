import Mathlib

namespace MathlibPlus.Open.AnalyticNumberTheory

def explicitModulusUniformBoundClaim8294 : Prop :=
  ∀ (N : ℕ),
    2 ≤ N →
      ∀ (u : ℝ),
        0 < u →
          u ≤ (1 / 2 : ℝ) →
            let q : ℝ := u / (1 - Real.exp (-u * (N : ℝ)))
            let M : ℝ → ℝ := fun t =>
              ∑' b : ℕ,
                if Nat.Coprime b N then
                  ((ArithmeticFunction.moebius b : ℤ) : ℝ) / (b : ℝ) *
                    Real.exp (-(t * (b : ℝ)))
                else 0
            let K : ℝ → ℝ → ℝ := fun x y =>
              ∑' a : ℕ,
                if Nat.Coprime a N then
                  Real.exp (-((a : ℝ) * y)) / (a : ℝ) * M ((a : ℝ) * x)
                else 0
            q ≤ (1 / 2 : ℝ) / (1 - Real.exp (-1)) ∧
              (1 / 2 : ℝ) / (1 - Real.exp (-1)) < (0.791 : ℝ) ∧
                |K (u * (N : ℝ)) u| < (2.57 : ℝ)

end MathlibPlus.Open.AnalyticNumberTheory
