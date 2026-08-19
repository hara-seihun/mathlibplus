import MathlibPlus.Open.Analysis.Claim7328ClosedTodaRatioLattice

namespace MathlibPlus.Open.ResearchFormalization.K0002Claim7327

noncomputable section

open MathlibPlus.Open.Analysis.Claim7328

/-- The normalized Hankel minor on the exact oriented confluent-Hankel carrier. -/
def normalizedD (H : ℕ → ℝ → ℝ) (m : ℕ) (t : ℝ) : ℝ :=
  H m t / H m 0

/-- The initial Toda ratio attached to the same flag. -/
def initialTodaRatio (H : ℕ → ℝ → ℝ) (m : ℕ) : ℝ :=
  H (m - 1) 0 * H (m + 1) 0 / (H m 0) ^ 2

/-- Claim 7327: on the even, all-order-smooth, positive initial Hankel flag,
the normalized minors satisfy the displayed Toda equation and initial data. -/
def claim_7327 : Prop :=
  ∀ F : ℝ → ℝ,
    Even F →
      (∀ n : ℕ, ContDiff ℝ n F) →
        let H : ℕ → ℝ → ℝ :=
          MathlibPlus.Analysis.Claim7317.orientedConfluentHankelMinor_claim7317 F
        initialFlagPositive7328 H →
          (∀ m : ℕ, 1 ≤ m → ∀ t : ℝ,
            -(deriv
                (fun u => deriv (fun v => Real.log (normalizedD H m v)) u) t) =
                initialTodaRatio H m *
                  normalizedD H (m - 1) t * normalizedD H (m + 1) t /
                    (normalizedD H m t) ^ 2 ∧
              normalizedD H m 0 = 1 ∧
              deriv (normalizedD H m) 0 = 0)

end

end MathlibPlus.Open.ResearchFormalization.K0002Claim7327
