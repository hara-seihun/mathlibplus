import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Analysis.ResearchSquaredXiSeries

noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable

def completedXi (s : ℂ) : ℂ :=
  (1 / 2 : ℂ) * s * (s - 1) * Complex.cpow (Real.pi : ℂ) (-s / 2) *
    Complex.Gamma (s / 2) * riemannZeta s

def squaredCriticalXi (z : ℂ) : ℂ :=
  completedXi ((1 / 2 : ℂ) + Complex.sqrt z)

def normalizedSquaredCriticalXi (z : ℂ) : ℂ :=
  squaredCriticalXi z / squaredCriticalXi 0

def oneZeroDeflation (gamma : ℝ) (z : ℂ) : ℂ :=
  normalizedSquaredCriticalXi z / (1 + z / (gamma : ℂ) ^ 2)

/-- Claim 4347: Xi symmetry makes the square-root pullback an even-variable
entire series, with the displayed normalization. -/
def squaredCriticalLineXiSeries_claim4347 : Prop :=
  completedXi (1 / 2 : ℂ) ≠ 0 ∧
    (∀ z : ℂ,
      completedXi ((1 / 2 : ℂ) + Complex.sqrt z) =
        completedXi ((1 / 2 : ℂ) - Complex.sqrt z)) ∧
    ∃ e : ℕ → ℂ,
      e 0 = 1 ∧
      ∀ z : ℂ, HasSum (fun n : ℕ => e n * z ^ n)
        (normalizedSquaredCriticalXi z)

/-- Claim 4348: the original normalized series and every critical-line
one-zero deflation are retained simultaneously, each with its own power
series coefficients. -/
def oneCriticalLineZeroDeflation_claim4348 : Prop :=
  completedXi (1 / 2 : ℂ) ≠ 0 ∧
    (∃ e : ℕ → ℂ,
      e 0 = 1 ∧
      ∀ z : ℂ, HasSum (fun n : ℕ => e n * z ^ n)
        (normalizedSquaredCriticalXi z)) ∧
    (∀ gamma : ℝ,
      completedXi ((1 / 2 : ℂ) + Complex.I * (gamma : ℂ)) = 0 →
      ∃ eGamma : ℕ → ℂ,
        ∀ z : ℂ, HasSum (fun n : ℕ => eGamma n * z ^ n)
          (oneZeroDeflation gamma z))

end
end MathlibPlus.Open.Analysis.ResearchSquaredXiSeries
