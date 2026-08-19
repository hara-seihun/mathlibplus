import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting

/-!
Statement-fidelity registry node for the final C-0044 tail comparison.  The
fractional powers in the asymptotic comparison are represented by `Real.rpow`.
-/

/-- The `L ≥ 3000` lower bound for `B₋`, its endpoint margin, and the
monotonicity certificate for the comparison factor. -/
noncomputable def finalAsymptoticComparison : Prop :=
  let eta : ℝ := 0.024334
  let c : ℝ := 1673823191040000 / 23
  let Bminus : ℝ → ℝ := fun L =>
    eta / L ^ 3 + eta / L ^ 4 + 5 * eta / L ^ 5 + 1057.2 / L ^ 7 -
      (∑ j ∈ Finset.Icc 8 15, (Nat.factorial j : ℝ) / L ^ j) -
      c / L ^ 16
  let comparisonFactor : ℝ → ℝ := fun L =>
    Real.rpow L (9 / 2 : ℝ) *
      Real.exp (-0.84768363 * Real.sqrt L)
  (∀ L : ℝ, 3000 ≤ L → Bminus L > eta / (2 * L ^ 3)) ∧
    eta / (2 * (3000 : ℝ) ^ 3) -
        9.2211 * Real.rpow (3000 : ℝ) (3 / 2 : ℝ) *
          Real.exp (-0.84768363 * Real.sqrt 3000) >
      (4.4024 : ℝ) / 10 ^ (13 : ℕ) ∧
    0.84768363 * Real.sqrt 3000 > 9 ∧
    StrictAntiOn comparisonFactor (Set.Ici 3000)

end MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting
