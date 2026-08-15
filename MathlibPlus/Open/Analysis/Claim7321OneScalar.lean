import MathlibPlus.Analysis.Claim7317

noncomputable section

namespace MathlibPlus.Open.Analysis

/-- One-scalar induction criterion for the oriented confluent Hankel flag. -/
def claim7321_oneScalarInductionCriterion : Prop :=
  ∀ (F : ℝ → ℝ),
    (∀ n : ℕ, ContDiff ℝ n F) →
      ∀ m : ℕ, 0 < m →
        let H : ℕ → ℝ → ℝ :=
          fun n t =>
            MathlibPlus.Analysis.Claim7317.orientedConfluentHankelMinor_claim7317
              F n t
        let r : ℕ → ℝ → ℝ :=
          fun n t => H (n + 1) t * H (n - 1) t / (H n t) ^ 2
        (∀ t : ℝ,
            0 < H (m - 1) t →
              0 < H m t →
                H (m + 1) t =
                    ((deriv (H m) t) ^ 2 -
                        H m t * deriv (fun u => deriv (H m) u) t) /
                      H (m - 1) t ∧
                  ((deriv (H m) t) ^ 2 -
                        H m t * deriv (fun u => deriv (H m) u) t) /
                      H (m - 1) t =
                    r m t * (H m t) ^ 2 / H (m - 1) t) ∧
          ((∀ k : ℕ, 1 ≤ k → k ≤ m → ∀ t : ℝ, 0 < H k t) →
            ((∀ t : ℝ, 0 < H (m + 1) t) ↔
              (∀ t : ℝ, 0 < r m t))) ∧
          (∀ t : ℝ, 0 < H m t →
            r m t =
                -deriv
                  (fun u => deriv (fun v => Real.log (H m v)) u) t ∧
              (0 < r m t ↔
                0 < -deriv
                  (fun u => deriv (fun v => Real.log (H m v)) u) t))

end MathlibPlus.Open.Analysis
