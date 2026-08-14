import Mathlib

namespace MathlibPlus.Open.NewResearch2.ModularLaguerre

noncomputable section
open scoped BigOperators

/-- Generalized Laguerre polynomials, specified by their standard three-term recurrence. -/
def generalizedLaguerre (n : ℕ) (α : ℝ) : Polynomial ℝ :=
  match n with
  | 0 => 1
  | 1 => Polynomial.C (α + 1) - Polynomial.X
  | n + 2 =>
      ((n + 2 : ℕ) : ℝ)⁻¹ •
        ((Polynomial.C (2 * (n : ℝ) + 3 + α) - Polynomial.X) *
            generalizedLaguerre (n + 1) α -
          Polynomial.C ((n : ℝ) + 1 + α) * generalizedLaguerre n α)

def modularLaguerreCoefficient (n : ℕ) (α : ℝ) : ℝ :=
  ∑' m : ℤ,
    Real.exp (-Real.pi * (m : ℝ) ^ 2) *
      (generalizedLaguerre n α).eval (Real.pi * (m : ℝ) ^ 2)

def scaledModularLaguerreCoefficient (n : ℕ) (α y : ℝ) : ℝ :=
  ∑' m : ℤ,
    Real.exp (-Real.pi * (m : ℝ) ^ 2 * y) *
      (generalizedLaguerre n α).eval (Real.pi * (m : ℝ) ^ 2 * y)

def claim4670_modular_laguerre_coefficient
    (A : ℝ) (n : ℕ) (α : ℝ) : Prop :=
  A = ∑' m : ℤ,
    Real.exp (-Real.pi * (m : ℝ) ^ 2) *
      (generalizedLaguerre n α).eval (Real.pi * (m : ℝ) ^ 2)

def claim4671_scaled_modular_laguerre_coefficient
    (A : ℝ → ℝ) (n : ℕ) (α : ℝ) : Prop :=
  (∀ y : ℝ, 0 < y →
    A y = ∑' m : ℤ,
      Real.exp (-Real.pi * (m : ℝ) ^ 2 * y) *
        (generalizedLaguerre n α).eval (Real.pi * (m : ℝ) ^ 2 * y)) ∧
  A 1 = modularLaguerreCoefficient n α

def normalizedLaguerreMoment (n : ℕ) (α : ℝ) : ℝ :=
  (Nat.factorial n : ℝ) * modularLaguerreCoefficient n α

def claim4672_moment_normalization
    (M : ℝ) (n : ℕ) (α : ℝ) : Prop :=
  M = (Nat.factorial n : ℝ) * modularLaguerreCoefficient n α

end
end MathlibPlus.Open.NewResearch2.ModularLaguerre
