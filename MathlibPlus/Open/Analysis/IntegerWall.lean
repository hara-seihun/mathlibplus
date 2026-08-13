import Mathlib

open scoped BigOperators Interval
open MeasureTheory

namespace MathlibPlus.Open.Analysis.IntegerWall

/-! Exact formalization of the reciprocal-Laplace integer-wall identities.
The packet's `W_n`, `X`, and `Y` are local functions here so that the registry
nodes retain their source formulas without introducing an unreviewed library
interface. -/

/-- Claims 14435 and 47504: the exact integer-wall formula and its moving
    two-atom decomposition, with the stated endpoint inequalities. -/
def integerWallTwoAtomReduction_claim14435_47504 : Prop :=
  let a : ℝ := 5 / 4
  let u : ℝ → ℝ := fun t ↦ Real.exp (-t)
  let X : ℝ → ℝ := fun t ↦ Real.exp (-Real.pi * Real.exp (-t))
  let Y : ℝ → ℝ := fun t ↦ Real.exp (-Real.pi * Real.exp t)
  let W : ℕ → ℝ → ℝ := fun n t ↦
    Real.exp (-a * t - Real.pi * (n : ℝ) ^ 2 * Real.exp (-t)) +
      Real.exp (a * t - Real.pi * (n : ℝ) ^ 2 * Real.exp t)
  (∀ (n : ℕ) (t : ℝ), 0 < n →
      W n t =
        Real.exp (-(5 / 4 : ℝ) * t - Real.pi * (n : ℝ) ^ 2 * Real.exp (-t)) +
          Real.exp ((5 / 4 : ℝ) * t - Real.pi * (n : ℝ) ^ 2 * Real.exp t)) ∧
  (∀ (n : ℕ) (t : ℝ), 0 < n →
      W n t =
        Real.exp (-a * t) * X t ^ (n ^ 2) +
          Real.exp (a * t) * Y t ^ (n ^ 2)) ∧
  StrictMono X ∧ StrictAnti Y ∧
  ∀ (t : ℝ), 0 < t →
    0 < Y t ∧ Y t < Real.exp (-Real.pi) ∧
      Real.exp (-Real.pi) < X t ∧ X t < 1

/-- Claim 47667: the reciprocal interval-Laplace integral has the displayed
    derivative and endpoint decomposition. -/
noncomputable def integerWallLaplaceDerivative_claim47667 : Prop :=
  let a : ℝ := 5 / 4
  let u : ℝ → ℝ := fun t ↦ Real.exp (-t)
  let v : ℝ → ℝ := fun t ↦ Real.exp t
  let X : ℝ → ℝ := fun t ↦ Real.exp (-Real.pi * Real.exp (-t))
  let Y : ℝ → ℝ := fun t ↦ Real.exp (-Real.pi * Real.exp t)
  let W : ℕ → ℝ → ℝ := fun n t ↦
    Real.exp (-a * t - Real.pi * (n : ℝ) ^ 2 * Real.exp (-t)) +
      Real.exp (a * t - Real.pi * (n : ℝ) ^ 2 * Real.exp t)
  let I : ℕ → ℝ → ℝ := fun n t ↦
    ∫ x in u t..v t,
      Real.rpow x (a - 1) *
        Real.exp (-Real.pi * (n : ℝ) ^ 2 * x)
  ∀ (n : ℕ) (t : ℝ), 0 < n → 0 < t →
    HasDerivAt (I n)
      (Real.rpow (u t) a * Real.exp (-Real.pi * (n : ℝ) ^ 2 * u t) +
        Real.rpow (v t) a * Real.exp (-Real.pi * (n : ℝ) ^ 2 * v t)) t ∧
    Real.rpow (u t) a * Real.exp (-Real.pi * (n : ℝ) ^ 2 * u t) +
        Real.rpow (v t) a * Real.exp (-Real.pi * (n : ℝ) ^ 2 * v t) = W n t ∧
    W n t =
      Real.exp (-a * t) * X t ^ (n ^ 2) +
        Real.exp (a * t) * Y t ^ (n ^ 2)

/-- Claim 47675: pointwise endpoint dominance for the reciprocal wall kernel. -/
def integerWallPointwiseDominance_claim47675 : Prop :=
  let a : ℝ := 5 / 4
  let X : ℝ → ℝ := fun t ↦ Real.exp (-Real.pi * Real.exp (-t))
  let Y : ℝ → ℝ := fun t ↦ Real.exp (-Real.pi * Real.exp t)
  StrictMono X ∧ StrictAnti Y ∧
  ∀ (n : ℕ) (t : ℝ), 0 < n → 0 < t →
    0 < Y t ∧ Y t < Real.exp (-Real.pi) ∧
      Real.exp (-Real.pi) < X t ∧ X t < 1 ∧
      Real.exp (2 * a * t - Real.pi * (n : ℝ) ^ 2 *
        (Real.exp t - Real.exp (-t))) < 1

end MathlibPlus.Open.Analysis.IntegerWall
