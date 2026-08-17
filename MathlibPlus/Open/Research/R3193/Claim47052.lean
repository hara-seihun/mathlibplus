import MathlibPlus.Open.Research.R3193.Claim47053

namespace MathlibPlus.Open.Research.R3193

/-- Claim 47052: the exact combined-score defect identity and its explicit
negative instance in the reviewed shared-bit Rademacher carrier. -/
def claim47052 : Prop :=
  (∀ (n : ℕ), 0 < n → ∀ j : Fin n,
    deltaW n j + deltaV n j - V n =
      (1 + ((n : ℝ) - 1) * p ^ 2 *
        (-((n : ℝ) - 2) + (2 * (n : ℝ) - 1) * p)) /
        (n : ℝ) ^ 2) ∧
    (∃ j : Fin 9, fullBlockScore 9 j < V 9)

end MathlibPlus.Open.Research.R3193
