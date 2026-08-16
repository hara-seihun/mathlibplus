import Mathlib

namespace MathlibPlus.Open.NumberTheory.Claim14746

open scoped BigOperators

noncomputable section

/-- The character in the weight basis of the `k`th symmetric power. -/
noncomputable def character (k : ℕ) (z : ℂ) : ℂ :=
  ∑ r ∈ Finset.range (k + 1),
    z ^ ((k : ℤ) - 2 * (r : ℤ))

/-- The divisor-sum coefficient `σ₁₁(n)`. -/
noncomputable def sigma11 (n : ℕ) : ℂ :=
  ∑ d ∈ n.divisors, (d : ℂ) ^ 11

/-- The coefficient of `q^n` in `q ∏_{m≥1}(1-q^m)^24`. -/
noncomputable def deltaCoefficient (n : ℕ) : ℤ :=
  let deltaTrunc : PowerSeries ℤ :=
    PowerSeries.X * ∏ m ∈ Finset.Icc 1 n, (1 - PowerSeries.X ^ m) ^ 24
  PowerSeries.coeff n deltaTrunc

/-- The positive real normalization `n^(11/2)`. -/
noncomputable def halfPower (n : ℕ) : ℝ :=
  (n : ℝ) ^ (11 / 2 : ℝ)

/-- The normalized Eisenstein coefficient `A_n`. -/
noncomputable def normalizedEisenstein (n : ℕ) : ℂ :=
  sigma11 n / (halfPower n : ℂ)

/-- The normalized Delta coefficient `B_n`. -/
noncomputable def normalizedDelta (n : ℕ) : ℂ :=
  (deltaCoefficient n : ℂ) / (halfPower n : ℂ)

/--
The prime-power normalized Eisenstein and Delta coefficients are the
symmetric-power characters.  The second parameter is a unit Satake lift, with
its local trace fixed by the normalized Delta coefficient.
-/
def claim14746 : Prop :=
  ∀ p : ℕ, Nat.Prime p →
    ∀ α : ℂ,
      ‖α‖ = 1 ∧
        normalizedDelta p = α + α⁻¹ →
      ∀ k : ℕ,
        normalizedEisenstein (p ^ k) =
            character k (halfPower p : ℂ) ∧
          normalizedDelta (p ^ k) = character k α

end

end MathlibPlus.Open.NumberTheory.Claim14746
