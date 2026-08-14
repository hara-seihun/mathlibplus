import Mathlib

namespace MathlibPlus.Open.Analysis

noncomputable def mellinPositivePower_claim3740 (a : ℝ) (s : ℂ) : ℂ :=
  Complex.exp (s * (Real.log a : ℂ))

noncomputable def mellinM_claim3740 (s : ℂ) : ℂ :=
  if s = 0 then
    2 * (Real.log 2 : ℂ) - (Real.log 3 : ℂ)
  else
    (2 * mellinPositivePower_claim3740 2 s -
      mellinPositivePower_claim3740 3 s - 1) / s

def reflected_mellin_quotient_asymptotic_claim3740 : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ m₀ : ℕ,
    ∀ m : ℕ, m₀ ≤ m → Odd m →
      ∀ u : ℂ, ‖u‖ ≤ (1 / 3 : ℝ) →
        ∃ e : ℂ,
          ‖e‖ ≤ C * (2 / 3 : ℝ) ^ m ∧
          mellinM_claim3740 ((m : ℂ) + u) /
              mellinM_claim3740 (1 - ((m : ℂ) + u)) =
            -mellinPositivePower_claim3740 3 ((m : ℂ) + u) *
                (((m : ℂ) + u) - 1) / ((m : ℂ) + u) * (1 + e)

noncomputable def poissonWeight_claim4227 (x : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-x) * x ^ n / (n.factorial : ℝ)

noncomputable def poissonM0_claim4227 (x : ℝ) (u : ℕ → ℂ) : ℝ :=
  Real.sqrt (∑' n : ℕ, poissonWeight_claim4227 x n * ‖u n‖ ^ 2)

noncomputable def poissonM1_claim4227 (x : ℝ) (u : ℕ → ℂ) : ℝ :=
  Real.sqrt (∑' n : ℕ, poissonWeight_claim4227 x n * ‖u (n + 1)‖ ^ 2)

noncomputable def poissonGraphNorm_claim4227 (x : ℝ) (u : ℕ → ℂ) : ℝ :=
  Real.sqrt (poissonM0_claim4227 x u ^ 2 + poissonM1_claim4227 x u ^ 2)

def poissonGraphFinite_claim4227 (x : ℝ) (u : ℕ → ℂ) : Prop :=
  Summable (fun n : ℕ =>
    poissonWeight_claim4227 x n * ‖u n‖ ^ 2) ∧
  Summable (fun n : ℕ =>
    poissonWeight_claim4227 x n * ‖u (n + 1)‖ ^ 2)

def shifted_cross_term_estimate_claim4227 : Prop :=
  ∀ (x : ℝ) (u v : ℕ → ℂ),
    0 < x →
    poissonGraphFinite_claim4227 x u →
    poissonGraphFinite_claim4227 x v →
    (∑' n : {n : ℕ // 1 ≤ n},
      poissonWeight_claim4227 x n.1 * ‖u n.1 * v (n.1 + 2)‖) ≤
        Real.sqrt 2 * poissonM1_claim4227 x u * poissonM1_claim4227 x v ∧
    poissonWeight_claim4227 x 0 * ‖u 0 * v 2‖ ≤
      x ^ (-(1 / 2 : ℝ)) * poissonM0_claim4227 x u * poissonM1_claim4227 x v

end MathlibPlus.Open.Analysis
