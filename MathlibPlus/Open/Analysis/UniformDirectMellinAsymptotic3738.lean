import Mathlib

namespace MathlibPlus.Open.Analysis

noncomputable section

/-- The two-step source function `1_[1,2] - 1_[2,3]`. -/
def claim3738Q (x : ℝ) : ℝ := by
  classical
  exact (if x ∈ Set.Icc (1 : ℝ) 2 then 1 else 0) -
    (if x ∈ Set.Icc (2 : ℝ) 3 then 1 else 0)

/-- The positive-real interpretation of `a^s` for a complex Mellin variable. -/
def claim3738PositiveRealPow (a : ℝ) (s : ℂ) : ℂ :=
  Complex.exp (s * (Real.log a : ℂ))

/-- Mellin transform of `q` on `[1,3]`. -/
def claim3738M (s : ℂ) : ℂ :=
  ∫ x in (1 : ℝ)..3, (claim3738Q x : ℂ) *
    Complex.exp ((s - 1) * (Real.log x : ℂ))

/-- Uniform direct Mellin asymptotic for odd integral centers. -/
def uniformDirectMellinAsymptotic3738 : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ,
    ∀ m : ℕ, Odd m → N ≤ m →
      ∀ u : ℂ, ‖u‖ ≤ (1 : ℝ) / 3 →
        ∃ e : ℂ,
          claim3738M ((m : ℂ) + u) =
            -(claim3738PositiveRealPow 3 ((m : ℂ) + u) /
                ((m : ℂ) + u)) * (1 + e) ∧
          ‖e‖ ≤ C * (((2 : ℝ) / 3) ^ m)

end
end MathlibPlus.Open.Analysis
