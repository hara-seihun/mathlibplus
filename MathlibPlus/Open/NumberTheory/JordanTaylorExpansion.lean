import Mathlib

namespace MathlibPlus.Open

/-- Jordan's divisor-sum coefficients are the Taylor coefficients of the
    corrected exponential divisor sum. -/
def jordanTaylorExpansionClaim8331 : Prop :=
  ∀ k : ℕ,
    let μ : ℕ → ℝ := fun d => ((ArithmeticFunction.moebius d : ℤ) : ℝ)
    let J : ℕ → ℝ := fun j =>
      (∑ d ∈ Nat.divisors k, μ d * (((k / d : ℕ) : ℝ) ^ j))
    let Δ : ℝ → ℝ := fun y =>
      (∑ d ∈ Nat.divisors k,
        μ d * Real.exp (-y * ((k / d : ℕ) : ℝ)))
    (∀ y : ℝ,
      Δ y = ∑' j : ℕ, ((-y) ^ j / (Nat.factorial j : ℝ)) * J j) ∧
      J 0 = if k = 1 then 1 else 0

end MathlibPlus.Open
