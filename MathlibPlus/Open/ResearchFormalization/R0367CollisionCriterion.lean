import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0367CollisionCriterion

noncomputable section

open scoped BigOperators

def gapAt (x : ℝ → ℤ → ℝ) (t : ℝ) (k : ℤ) : ℝ :=
  x t (k + 1) - x t k

def pressureTermAt (x : ℝ → ℤ → ℝ) (t : ℝ) (k j : ℤ) : ℝ :=
  ((x t (k + 1) - x t j) * (x t k - x t j))⁻¹

def pressureAt (x : ℝ → ℤ → ℝ) (t : ℝ) (k : ℤ) : ℝ :=
  2 - gapAt x t k ^ 2 *
    ∑' j : {j : ℤ // j ≠ k ∧ j ≠ k + 1}, pressureTermAt x t k j.1

def pressureBound (R : ℕ) (μ : ℝ) : ℝ :=
  2 / ((R : ℝ) + 1) +
    (μ / 6) * (R : ℝ) * (4 * (R : ℝ) + 5) / ((R : ℝ) + 1)

/-- The zero-flow differential law for one adjacent squared gap. -/
def squaredGapZeroFlow
    (x : ℝ → ℤ → ℝ) (k : ℤ) (τ T : ℝ) : Prop :=
  ∀ s : ℝ, τ ≤ s → s ≤ T →
    HasDerivAt (fun t : ℝ => gapAt x t k ^ 2)
      (4 * pressureAt x s k) s

/-- A scalar pressure certificate on the complete interval. -/
def scalarPressureCertificate
    (x : ℝ → ℤ → ℝ) (k : ℤ) (R : ℕ) (μ τ T : ℝ) : Prop :=
  1 ≤ R ∧
    0 ≤ μ ∧
    τ ≤ T ∧
    ∀ s : ℝ, τ ≤ s → s ≤ T →
      pressureAt x s k ≤ pressureBound R μ

/-- Claim 25651: the zero-flow derivative law and the same scalar pressure
certificate integrate to the exact terminal-gap bound and its strict
noncollision consequence. -/
def claim25651 : Prop :=
  ∀ (x : ℝ → ℤ → ℝ) (k : ℤ) (R : ℕ) (μ τ T : ℝ),
    squaredGapZeroFlow x k τ T →
      scalarPressureCertificate x k R μ τ T →
        gapAt x τ k ^ 2 ≥
            gapAt x T k ^ 2 -
              4 * (T - τ) * max (pressureBound R μ) 0 ∧
          (4 * (T - τ) * max (pressureBound R μ) 0 <
              gapAt x T k ^ 2 →
            ∀ s : ℝ, τ ≤ s → s ≤ T → gapAt x s k ≠ 0)

end
end MathlibPlus.Open.ResearchFormalization.R0367CollisionCriterion
