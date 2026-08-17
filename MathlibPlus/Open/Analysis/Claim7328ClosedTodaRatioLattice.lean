import MathlibPlus.Analysis.Claim7317

noncomputable section

namespace MathlibPlus.Open.Analysis.Claim7328

/-- The ratio lattice with the source boundary value at index zero. -/
def closedTodaRatio7328 (H : ℕ → ℝ → ℝ) (m : ℕ) (t : ℝ) : ℝ :=
  match m with
  | 0 => 0
  | k + 1 => H (k + 2) t * H k t / (H (k + 1) t) ^ 2

/-- Positivity of the initial oriented Hankel flag on the real variable. -/
def initialFlagPositive7328 (H : ℕ → ℝ → ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ t : ℝ, 0 < H k t

/-- Claim 7328: the oriented confluent Hankel flag carries the closed
Toda-ratio lattice on its positive initial-flag domain. -/
def claim7328_closedTodaRatioLattice : Prop :=
  ∀ (F : ℝ → ℝ),
    (∀ n : ℕ, ContDiff ℝ n F) →
      let H : ℕ → ℝ → ℝ :=
        MathlibPlus.Analysis.Claim7317.orientedConfluentHankelMinor_claim7317 F
      let r : ℕ → ℝ → ℝ := closedTodaRatio7328 H
      initialFlagPositive7328 H →
        (∀ t : ℝ, r 0 t = 0) ∧
          (∀ m : ℕ, 1 ≤ m → ∀ t : ℝ,
            r m t = H (m + 1) t * H (m - 1) t / (H m t) ^ 2 ∧
              H (m + 1) t * H (m - 1) t / (H m t) ^ 2 =
                -deriv
                  (fun u => deriv (fun v => Real.log (H m v)) u) t) ∧
          (∀ m : ℕ, 1 ≤ m → ∀ t : ℝ,
            deriv (fun u => deriv (fun v => Real.log (r m v)) u) t =
              -(r (m + 1) t - 2 * r m t + r (m - 1) t))

end MathlibPlus.Open.Analysis.Claim7328

end
