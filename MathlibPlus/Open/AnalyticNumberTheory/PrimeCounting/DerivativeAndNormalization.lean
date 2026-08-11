import Mathlib

namespace MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting

/-!
Statement-fidelity registry nodes for admitted prime-counting derivative and
normalization certificates.  Ellipsized decimals are kept as half-open
prefix intervals.
-/

/-- Claim 778: the exact derivative identity for the improved eight-term
majorant associated with the coefficient `δ = 0.0145407`. -/
def exactDerivativeIdentityDelta : Prop :=
  let δ : ℝ := 0.0145407
  let F : ℝ → ℝ := fun x =>
    let L := Real.log x
    x / L + x / L ^ (2 : ℕ) + 2 * x / L ^ (3 : ℕ) +
      6.0145407 * x / L ^ (4 : ℕ) + 24 * x / L ^ (5 : ℕ) +
      120 * x / L ^ (6 : ℕ) + 720 * x / L ^ (7 : ℕ) +
      6097.2 * x / L ^ (8 : ℕ)
  let Q : ℝ → ℝ := fun L =>
    L ^ (8 : ℕ) + δ * L ^ (5 : ℕ) - 4 * δ * L ^ (4 : ℕ) +
      1057.2 * L - 48777.6
  ∀ x : ℝ, 1 < x →
    let L := Real.log x
    let displayed :=
      1 / L + δ / L ^ (4 : ℕ) - 4 * δ / L ^ (5 : ℕ) +
        1057.2 / L ^ (8 : ℕ) - 48777.6 / L ^ (9 : ℕ)
    HasDerivAt F displayed x ∧ displayed = Q L / L ^ (9 : ℕ)

/-- Claim 794: directed normalization inequalities and the two certified
strict margins. -/
def directedNormalizationInequalities : Prop :=
  let R : ℝ := 5.5666305
  let cstar : ℝ := 121.096 / Real.rpow R (3 / 2 : ℝ)
  let dstar : ℝ := 2 / Real.sqrt R
  9.2210558813513077 ≤ cstar ∧
    cstar < 9.2210558813513078 ∧
    cstar < 9.221056 ∧
    0.8476836336683192 ≤ dstar ∧
    dstar < 0.8476836336683193 ∧
    0.84768363 < dstar ∧
    1.18648 / 10 ^ (7 : ℕ) < 9.221056 - cstar ∧
    3.6683 / 10 ^ (9 : ℕ) < dstar - 0.84768363

end MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting
