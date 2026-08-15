import Mathlib

namespace MathlibPlus.Open.Analysis

noncomputable def stieltjesLaurentConvention (γ : ℕ → ℝ) : Prop :=
  ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < 1 →
    riemannZeta (1 + z) =
      1 / z + ∑' n : ℕ,
        ((-1 : ℂ) ^ n) * (γ n : ℂ) * z ^ n /
          (Nat.factorial n : ℂ)

noncomputable def stieltjesConstants : ℕ → ℝ :=
  Classical.epsilon stieltjesLaurentConvention

noncomputable def stieltjesAlpha : ℝ := -stieltjesConstants 1

noncomputable def stieltjesZ (t : ℝ) : ℝ :=
  (deriv riemannZeta (1 + (t : ℂ))).re + 1 / t ^ 2

def stieltjesContext : Prop :=
  stieltjesLaurentConvention stieltjesConstants

end MathlibPlus.Open.Analysis
