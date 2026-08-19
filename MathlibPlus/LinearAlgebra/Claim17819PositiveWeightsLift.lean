import Mathlib

open scoped BigOperators

noncomputable section

namespace MathlibPlus.LinearAlgebra.Claim17819

private def intervalReflection17819
    (N a b : ℕ) (i j : Fin N) : ℝ :=
  if i.1 + j.1 = a + b - 1 ∧
      a ≤ i.1 ∧ i.1 ≤ b - 1 ∧
      a ≤ j.1 ∧ j.1 ≤ b - 1 then
    (b - a : ℝ)
  else 0

private def cN17819 (N : ℕ) (h : ℕ → ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j =>
    ∑' a : ℕ, ∑' b : ℕ,
      if a < b then
        h a * h b * intervalReflection17819 N a b i j
      else 0

def positiveWeights_give_nonnegative_lift_claim17819 : Prop :=
  ∀ (N : ℕ) (h : ℕ → ℝ),
    (∀ a : ℕ, 0 ≤ h a) →
      (∀ a b : ℕ, 0 ≤ h a * h b) ∧
        (∀ i j : Fin N, 0 ≤ cN17819 N h i j)

end MathlibPlus.LinearAlgebra.Claim17819

end
