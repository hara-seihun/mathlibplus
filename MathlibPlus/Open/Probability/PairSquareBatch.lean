import Mathlib

open scoped BigOperators

noncomputable section
namespace MathlibPlus.Open.Probability

private def directionalMass (p u d : ℝ) : Bool → Bool → ℝ
  | false, false => 1 - p
  | false, true => u / 2
  | true, false => d / 2
  | true, true => p - (u + d) / 2

private def oneDirectionFeasible (p u d : ℝ) : Prop :=
  (∀ a b, 0 ≤ directionalMass p u d a b) ∧
    (∑ a, ∑ b, directionalMass p u d a b) = 1

private def squareFreeCoupling (mi mj : Bool → Bool → ℝ) : Prop :=
  ∃ μ : (Bool × Bool) → (Bool × Bool) → ℝ,
    (∀ a b c d, 0 ≤ μ (a, b) (c, d)) ∧
    (∑ a, ∑ b, ∑ c, ∑ d, μ (a, b) (c, d) = 1) ∧
    (∀ a b, ∑ c, ∑ d, μ (a, b) (c, d) = mi a b) ∧
    (∀ c d, ∑ a, ∑ b, μ (a, b) (c, d) = mj c d) ∧
    μ (true, true) (true, true) = 0

/-- The complete pair square-free coupling criterion is exactly the pair influence inequality. -/
def completePairSquareCouplingCriterion : Prop :=
  ∀ p_i p_j u_ij d_ij u_ji d_ji : ℝ,
    (squareFreeCoupling (directionalMass p_i u_ij d_ij)
      (directionalMass p_j u_ji d_ji) ↔
      oneDirectionFeasible p_i u_ij d_ij ∧
      oneDirectionFeasible p_j u_ji d_ji ∧
      (p_i - (u_ij + d_ij) / 2) + (p_j - (u_ji + d_ji) / 2) ≤ 1) ∧
    ((p_i - (u_ij + d_ij) / 2) + (p_j - (u_ji + d_ji) / 2) ≤ 1 ↔
      p_i + p_j ≤ 1 + (u_ij + d_ij + u_ji + d_ji) / 2)

end MathlibPlus.Open.Probability
