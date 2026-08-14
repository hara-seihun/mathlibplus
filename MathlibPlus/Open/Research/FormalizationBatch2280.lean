import Mathlib

noncomputable section

namespace MathlibPlus.Open.Research

/-- The explicit sequence of real-entire quadratic functions in Claim 2280.
The formula is used only at positive natural indices, where the denominator is
literally `n`. -/
def claim2280_f (n : ℕ) (z : ℂ) : ℂ := z ^ 2 + 1 / (n : ℂ)

def claim2280_limit (z : ℂ) : ℂ := z ^ 2

def claim2280_root (n : ℕ) : ℂ :=
  Complex.I / (Real.sqrt (n : ℝ) : ℂ)

/-- Uniform convergence on every closed disk, restricted to the positive
indices occurring in the statement. -/
def claim2280_locallyUniform : Prop :=
  ∀ R ε : ℝ, 0 < R → 0 < ε →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 0 < n →
      ∀ z : ℂ, ‖z‖ ≤ R →
        ‖claim2280_f n z - claim2280_limit z‖ < ε

/-- Claim 2280: the displayed real-entire sequence is a counterexample to
stability of local hyperbolicity at a multiple real zero. -/
def claim_2280 : Prop :=
  (∀ n : ℕ, 0 < n → Differentiable ℂ (claim2280_f n)) ∧
  Differentiable ℂ claim2280_limit ∧
  (∀ n : ℕ, 0 < n → ∀ z : ℂ,
    claim2280_f n (star z) = star (claim2280_f n z)) ∧
  (∀ z : ℂ,
    claim2280_limit (star z) = star (claim2280_limit z)) ∧
  claim2280_locallyUniform ∧
  (∀ z : ℂ, claim2280_limit z = 0 → z.im = 0) ∧
  claim2280_limit 0 = 0 ∧
  deriv claim2280_limit 0 = 0 ∧
  claim2280_limit 1 = 1 ∧
  (∀ n : ℕ, 0 < n →
    claim2280_f n (claim2280_root n) = 0 ∧
    claim2280_f n (-claim2280_root n) = 0 ∧
    -claim2280_root n = star (claim2280_root n) ∧
    (claim2280_root n).im ≠ 0 ∧
    (-claim2280_root n).im ≠ 0) ∧
  (∀ R : ℝ, 0 < R → ∀ N : ℕ, ∃ n : ℕ,
    N ≤ n ∧ 0 < n ∧
    ‖claim2280_root n‖ < R ∧
    claim2280_f n (claim2280_root n) = 0 ∧
    (claim2280_root n).im ≠ 0)

end MathlibPlus.Open.Research
