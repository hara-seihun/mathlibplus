import Mathlib

open Filter
open MeasureTheory
open scoped BigOperators Topology

namespace MathlibPlus.Open.ResearchFormalization.O0322

noncomputable section

/-- The parameter-two Laguerre polynomial in the admitted transform carrier. -/
def laguerreTwo15367 (d : ℕ) (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (d + 1),
    (-1 : ℝ) ^ k * (Nat.choose (d + 2) (k + 2) : ℝ) *
      t ^ k / (k.factorial : ℝ)

/-- The fixed truncated exponential profile from the admitted statement. -/
def truncatedExponential15367 (δ T t : ℝ) : ℝ :=
  if T ≤ t then Real.exp (-δ * t) else 0

/-- The Laguerre transform of a real profile on the positive half-line. -/
def laguerreTransform15367 (B : ℝ → ℝ) (d : ℕ) : ℝ :=
  ∫ t in Set.Ioi (0 : ℝ), B t * laguerreTwo15367 d t

/-- A fixed truncated exponential has exponentially growing transforms below
    the one-half decay threshold, with the alternating eventual sign. -/
def claim15367 : Prop :=
  ∀ T : ℝ, 0 < T → ∀ δ : ℝ, 0 < δ → δ < 1 / 2 →
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ d : ℕ in atTop,
        c * ((1 - δ) / δ) ^ d ≤
            |laguerreTransform15367 (truncatedExponential15367 δ T) d| ∧
          0 < (-1 : ℝ) ^ d *
            laguerreTransform15367 (truncatedExponential15367 δ T) d

end

end MathlibPlus.Open.ResearchFormalization.O0322
