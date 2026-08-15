import Mathlib

namespace MathlibPlus.Open.Analysis

noncomputable def greenPhiRaw (u : ℝ) : ℝ :=
  ∑' n : ℕ,
    (4 * Real.pi ^ 2 * (n : ℝ) ^ 4 * Real.exp (9 * u / 2) -
        6 * Real.pi * (n : ℝ) ^ 2 * Real.exp (5 * u / 2)) *
      Real.exp (-Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * u))

noncomputable def greenPhi (u : ℝ) : ℝ :=
  greenPhiRaw |u|

noncomputable def greenACoefficient (n : ℕ) : ℝ :=
  (2 / (Nat.factorial (2 * n) : ℝ)) *
    ∫ u in Set.Ioi (0 : ℝ), greenPhi u * u ^ (2 * n)

noncomputable def greenA (z : ℂ) : ℂ :=
  ∑' n : ℕ, (greenACoefficient n : ℂ) * z ^ n

noncomputable def greenPhiGamma (γ u : ℝ) : ℝ :=
  γ * ∫ v in Set.Ioi u, greenPhi v * Real.sin (γ * (v - u))

noncomputable def greenBoundaryCosineIntegral (γ : ℝ) : ℝ :=
  ∫ v in Set.Ioi (0 : ℝ), greenPhi v * Real.cos (γ * v)

def criticalLineZeroGreenBoundary : Prop :=
  ∀ γ : ℝ, 0 < γ → greenA (-(γ : ℂ) ^ 2) = 0 →
    HasDerivAt (greenPhiGamma γ)
        (-γ ^ 2 * greenBoundaryCosineIntegral γ) 0 ∧
      greenA (-(γ : ℂ) ^ 2) =
        (2 * greenBoundaryCosineIntegral γ : ℂ) ∧
      ((-γ ^ 2 * greenBoundaryCosineIntegral γ : ℝ) : ℂ) =
        -((γ : ℂ) ^ 2 / 2) * greenA (-(γ : ℂ) ^ 2) ∧
      -((γ : ℂ) ^ 2 / 2) * greenA (-(γ : ℂ) ^ 2) = 0 ∧
      (∀ u : ℝ,
        iteratedDeriv 2 (greenPhiGamma γ) u +
            γ ^ 2 * greenPhiGamma γ u = γ ^ 2 * greenPhi u) ∧
      (∀ u : ℝ, greenPhi (-u) = greenPhi u) ∧
      (∀ n : ℕ, Odd n → iteratedDeriv n (greenPhiGamma γ) 0 = 0)

end MathlibPlus.Open.Analysis
