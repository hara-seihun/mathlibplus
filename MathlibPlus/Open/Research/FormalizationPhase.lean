import Mathlib

namespace MathlibPlus.Open.Research

noncomputable section

/-- Restriction of a complex function to the horizontal trace at height `y`. -/
def horizontalTrace (B : ℂ → ℂ) (y x : ℝ) : ℂ :=
  B ((x : ℂ) + (y : ℂ) * Complex.I)

/-- Admitted half-turn phase-node theorem. -/
def claim3537 : Prop :=
  ∀ (B : ℂ → ℂ) (a b y V : ℝ) (θ : ℝ → ℝ),
    a ≤ b →
    0 < V →
    (∀ x : ℝ, x ∈ Set.Icc a b → horizontalTrace B y x ≠ 0) →
    ContinuousOn θ (Set.Icc a b) →
    (∀ x : ℝ, x ∈ Set.Icc a b →
      horizontalTrace B y x =
        Complex.exp (Complex.I * (θ x : ℂ)) *
          (‖horizontalTrace B y x‖ : ℂ)) →
    θ b - θ a = V →
    let n : ℕ := Int.toNat (Int.floor (V / Real.pi))
    ∃ x : Fin (n + 1) → ℝ,
      x 0 = a ∧
      (∀ i j : Fin (n + 1), i.1 < j.1 → x i < x j) ∧
      (∀ j : Fin (n + 1), x j ≤ b) ∧
      (∀ j : Fin (n + 1),
        horizontalTrace B y (x j) =
          (-1 : ℂ) ^ j.1 * Complex.exp (Complex.I * (θ a : ℂ)) *
            (‖horizontalTrace B y (x j)‖ : ℂ))

end

end MathlibPlus.Open.Research
