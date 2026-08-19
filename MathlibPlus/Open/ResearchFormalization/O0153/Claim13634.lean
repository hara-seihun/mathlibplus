import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.O0153.Claim13634

open Filter Asymptotics Topology

noncomputable section

/-- The positive real principal branch used for the Lambert location. -/
def principalLambertW (x : ℝ) : ℝ :=
  sInf {y : ℝ | 0 ≤ y ∧ y * Real.exp y = x}

/-- The phase fixed by the first-shell moment carrier. -/
def saddlePhase (n : ℕ) (u : ℝ) : ℝ :=
  (2 * (n : ℝ)) * Real.log u + u / 2 - Real.pi * Real.exp (2 * u)

/-- The second derivative of the displayed phase. -/
def saddleSecondDerivative (n : ℕ) (u : ℝ) : ℝ :=
  iteratedDeriv 2 (saddlePhase n) u

/-- The stationary equation for the positive saddle. -/
def saddleEquation (n : ℕ) (u : ℝ) : Prop :=
  2 * (n : ℝ) / u + (1 / 2 : ℝ) =
    2 * Real.pi * Real.exp (2 * u)

/-- Claim 13634: strict concavity, the unique positive maximizer, its exact
saddle equation, and both stated principal-Lambert asymptotics. -/
def claim13634 : Prop :=
  ∃ u : ℕ → ℝ,
    (∀ n : ℕ, 0 < n →
      ∀ v : ℝ, 0 < v →
        saddleSecondDerivative n v =
            -2 * (n : ℝ) / v ^ 2 - 4 * Real.pi * Real.exp (2 * v) ∧
          saddleSecondDerivative n v < 0) ∧
    (∀ n : ℕ, 0 < n →
      0 < u n ∧
        saddleEquation n (u n) ∧
        (∀ v : ℝ, 0 < v →
          saddlePhase n v ≤ saddlePhase n (u n) ∧
          (saddlePhase n v = saddlePhase n (u n) → v = u n))) ∧
    (∀ n : ℕ, 0 < n →
      Real.pi * (2 * u n) * Real.exp (2 * u n) =
        2 * (n : ℝ) + (2 * u n) / 4) ∧
    IsLittleO atTop
      (fun n : ℕ => 2 * u n - principalLambertW
        (2 * (n : ℝ) / Real.pi))
      (fun _ : ℕ => (1 : ℝ)) ∧
    Tendsto
      (fun n : ℕ =>
        u n / ((1 / 2 : ℝ) * principalLambertW
          (2 * (n : ℝ) / Real.pi)))
      atTop (𝓝 (1 : ℝ))

end

end MathlibPlus.Open.ResearchFormalization.O0153.Claim13634
