import Mathlib

open scoped BigOperators
open MeasureTheory

noncomputable section

namespace MathlibPlus.Open.Analysis.LaguerreFockCritical

/-- The generalized Laguerre polynomial `L_k^(2)` in the packet's normalization. -/
noncomputable def laguerreTwo (k : ℕ) (t : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (k + 1),
    (-1 : ℝ) ^ j * (Nat.choose (k + 2) (k - j) : ℝ) * t ^ j /
      (Nat.factorial j : ℝ)

/-- The integrated Laguerre discrepancy coefficients, including the two zero
initial coefficients. -/
noncomputable def discrepancyCoefficient (B : ℝ → ℝ) (n : ℕ) : ℝ :=
  if 2 ≤ n then
    ∫ t in Set.Ici (0 : ℝ), laguerreTwo (n - 2) t * B t
  else 0

/-- The square of the ordinary Poisson--Fock norm at parameter `x`. -/
noncomputable def mZeroXSquared (x : ℝ) (u : ℕ → ℝ) : ℝ :=
  ∑' n : ℕ,
    Real.exp (-x) * x ^ n * (abs (u n)) ^ 2 /
      (Nat.factorial n : ℝ)

/-- The ordinary Poisson--Fock norm whose square is the displayed weighted
series. -/
noncomputable def mZeroX (x : ℝ) (u : ℕ → ℝ) : ℝ :=
  Real.sqrt (mZeroXSquared x u)

/-- A measurable tail supported on `[T, ∞)` and obeying the stretched-
exponential envelope. -/
def admissibleTail (B : ℝ → ℝ) (α c T : ℝ) : Prop :=
  Measurable B ∧
    (∀ t : ℝ, t < T → B t = 0) ∧
    (∀ t : ℝ, T ≤ t → abs (B t) ≤ Real.exp (-c * t ^ α))

/-- Infinitude of the Poisson--Fock tail supremum. -/
def tailSupremumInfinite (x α c T : ℝ) : Prop :=
  ∀ R : ℝ, ∃ B : ℝ → ℝ,
    admissibleTail B α c T ∧
      R < mZeroX x (discrepancyCoefficient B)

/-- The tangent-minimization constant `C_{α,c}`. -/
noncomputable def tangentConstant (α c : ℝ) : ℝ :=
  c * (1 - α) * (c * α) ^ (α / (1 - α))

/-- The critical constant `c_*(x)`. -/
noncomputable def criticalConstant (x : ℝ) : ℝ :=
  (3 / 2 : ℝ) * x ^ (1 / 3 : ℝ)

/-- Claim 14372: at the critical exponent, every cutoff has an infinite
Poisson--Fock tail supremum below the strict critical constant, with the exact
tangent constant and leading-coefficient threshold. -/
def criticalSubcriticalObstruction_claim14372 : Prop :=
  ∀ x : ℝ, 0 < x →
    (∀ c : ℝ, 0 < c → c < criticalConstant x →
      ∀ T : ℝ,
        tailSupremumInfinite x (2 / 3 : ℝ) c T) ∧
    (∀ c : ℝ, 0 < c →
      tangentConstant (2 / 3 : ℝ) c = 4 * c ^ 3 / 27 ∧
        (0 < x / 2 - 4 * c ^ 3 / 27 ↔ c < criticalConstant x))

end MathlibPlus.Open.Analysis.LaguerreFockCritical

end
