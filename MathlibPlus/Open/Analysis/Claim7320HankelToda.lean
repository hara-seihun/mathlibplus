import Mathlib

noncomputable section

namespace MathlibPlus.Open.Analysis

/-- The unoriented confluent Hankel determinant appearing in Claim 7320. -/
def confluentHankelDet (F : ℝ → ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  Matrix.det (fun i j : Fin n => iteratedDeriv (i.1 + j.1) F t)

/-- The oriented minor, with the sign and zero-index normalization from Claim 7317. -/
def orientedConfluentHankelDet (F : ℝ → ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  (-1 : ℝ) ^ (n * (n - 1) / 2) * confluentHankelDet F n t

/-- Claim 7320: the contiguous Hankel/Toda identity in both orientations. -/
def claim7320_contiguousHankelTodaIdentity : Prop :=
  ∀ F : ℝ → ℝ,
    (∀ n : ℕ, ContDiff ℝ n F) →
      ∀ m : ℕ, 0 < m → ∀ t : ℝ,
        let τ := confluentHankelDet F
        let H := orientedConfluentHankelDet F
        (τ m t * deriv (fun u => deriv (τ m) u) t - (deriv (τ m) t) ^ 2 =
            τ (m - 1) t * τ (m + 1) t) ∧
          ((deriv (H m) t) ^ 2 - H m t * deriv (fun u => deriv (H m) u) t =
            H (m - 1) t * H (m + 1) t)

end MathlibPlus.Open.Analysis
