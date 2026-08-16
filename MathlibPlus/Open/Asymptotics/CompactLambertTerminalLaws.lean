import Mathlib

open Filter Asymptotics
open scoped Topology

namespace MathlibPlus.Open.Asymptotics

noncomputable section

/-- The positive-real defining relation used here for the principal Lambert branch. -/
private def principalPositiveLambertBranch (W₀ : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, 0 < x →
    0 < W₀ x ∧ W₀ x * Real.exp (W₀ x) = x

/-- The sampled sequence `W_j = W₀(j/(2π))`. -/
private def compactLambertSequence (W₀ : ℝ → ℝ) : ℕ → ℝ :=
  fun j => W₀ ((j : ℝ) / (2 * Real.pi))

/-- A multiplicative `1 + o(1)` relation for real sequences at `atTop`. -/
private def isOnePlusLittleO (f g : ℕ → ℝ) : Prop :=
  ∃ ε : ℕ → ℝ,
    Tendsto ε atTop (nhds 0) ∧
      ∀ᶠ n : ℕ in atTop, f n = g n * (1 + ε n)

/-- Claim 15198: additive convergence to the positive compact Lambert profile
implies convergence to the corresponding relative profile. -/
def additiveCompactLambertRelativeAsymptotics_15198 : Prop :=
  ∀ (a : ℕ → ℝ) (W₀ : ℝ → ℝ),
    principalPositiveLambertBranch W₀ →
      let W : ℕ → ℝ := compactLambertSequence W₀
      Tendsto
          (fun j : ℕ => 4 * (j : ℝ) * a j - W j)
          atTop (nhds 0) →
        Tendsto
          (fun j : ℕ =>
            a j / (W j / (4 * (j : ℝ))))
          atTop (nhds 1)

/-- Claim 15200: the exact primitive-ratio hypothesis, additive compact
Lambert hypothesis, and one-plus-little-o ratio hypothesis force the terminal
one-sixteenth law and its equivalent normalized limit. -/ 
def forcedOneSixteenthTerminalNormLaw_15200 : Prop :=
  ∀ (a h t rho : ℕ → ℝ) (W₀ : ℝ → ℝ),
    principalPositiveLambertBranch W₀ →
      let W : ℕ → ℝ := compactLambertSequence W₀
      (∀ n : ℕ, 1 ≤ n →
        h n / h (n - 1) = (a (2 * n - 1) * a (2 * n)) ^ 2) →
      Tendsto
          (fun j : ℕ => 4 * (j : ℝ) * a j - W j)
          atTop (nhds 0) →
      (∀ n : ℕ, 1 ≤ n → rho n = t n / t (n - 1)) →
      isOnePlusLittleO rho
        (fun n : ℕ => W (4 * n) ^ 2 / (16 * (n : ℝ) ^ 2)) →
      isOnePlusLittleO
          (fun n : ℕ => h n / h (n - 1))
          (fun n : ℕ => rho n ^ 2 / 16) ∧
        Tendsto
          (fun n : ℕ =>
            32 * h n / (h (n - 1) * rho n ^ 2))
          atTop (nhds (2 : ℝ))

/-- Claim 15201: for the principal compact Lambert model, the displayed
finite-index identity holds and its left-hand side tends to `2`. -/ 
def compactLambertModelIdentity_15201 : Prop :=
  ∀ (W₀ : ℝ → ℝ),
    principalPositiveLambertBranch W₀ →
      let W : ℕ → ℝ := compactLambertSequence W₀
      let aStar : ℕ → ℝ := fun j => W j / (4 * (j : ℝ))
      let rhoStar : ℕ → ℝ :=
        fun n => W (4 * n) ^ 2 / (16 * (n : ℝ) ^ 2)
      (∀ n : ℕ, 1 ≤ n →
        32 * (aStar (2 * n - 1) * aStar (2 * n)) ^ 2 /
            (rhoStar n) ^ 2 =
          (8 * (n : ℝ) ^ 2 /
            (((2 * n - 1 : ℕ) : ℝ) ^ 2)) *
            ((W (2 * n - 1) * W (2 * n)) /
              W (4 * n) ^ 2) ^ 2) ∧
      Tendsto
        (fun n : ℕ =>
          32 * (aStar (2 * n - 1) * aStar (2 * n)) ^ 2 /
            (rhoStar n) ^ 2)
        atTop (nhds (2 : ℝ))

end

end MathlibPlus.Open.Asymptotics
