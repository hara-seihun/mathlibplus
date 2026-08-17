import MathlibPlus.Open.Analysis.Claim3381

namespace MathlibPlus.Open.Analysis.Claim3386

/-- The scalar Toda curvature recurrence for the primitive completed-theta
    determinant tower, including its constant-base solution. -/
def exactScalarTodaCurvatureRecurrence : Prop :=
  let G : ℝ → ℝ := fun z => Real.log (1 - Real.exp (-z))
  let t : ℕ → ℝ :=
    MathlibPlus.Open.Analysis.Claim3381.primitiveCompletedThetaMoment
  (∀ n : ℕ,
      MathlibPlus.Open.Analysis.Claim3381.L 0 n = 0) ∧
    (∀ m n : ℕ, 1 ≤ m →
      MathlibPlus.Open.Analysis.Claim3381.L (m + 1) n =
        2 * MathlibPlus.Open.Analysis.Claim3381.L m n -
          MathlibPlus.Open.Analysis.Claim3381.L (m - 1) n -
          MathlibPlus.Open.Analysis.Claim3381.secondDifference
            (fun k => G (MathlibPlus.Open.Analysis.Claim3381.L m k)) n) ∧
    (∀ n : ℕ,
      MathlibPlus.Open.Analysis.Claim3381.L 1 n =
        -MathlibPlus.Open.Analysis.Claim3381.secondDifference
          (fun k => Real.log (t k)) n) ∧
    (∀ c : ℝ, (∀ n : ℕ,
        MathlibPlus.Open.Analysis.Claim3381.L 1 n = c) →
      ∀ m n : ℕ,
        MathlibPlus.Open.Analysis.Claim3381.L m n = (m : ℝ) * c)

end MathlibPlus.Open.Analysis.Claim3386
