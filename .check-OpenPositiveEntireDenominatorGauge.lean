import Mathlib

namespace MathlibPlus.Open.Analysis

noncomputable section

/--
Claim 11524.  For every `0 < r < 1` and `0 < θ < π/2`, the explicitly
constructed gauge is entire, even, real on the real axis, two-periodic, and
strictly positive there, while its zeros are the displayed off-axis quartet.

Because the factors are two-periodic, the four displayed zeros are
representatives modulo translation by `2`; the formal zero clause includes all
integer translates.  The source's decimal for the special choice
`r = 1/2, θ = π/3` is treated as an approximation to the exact height
`log 2 / π`, not as an exact equality of real numerals.  The final clause
formalizes the stated preservation of the reciprocal two-step ratio for an
arbitrary source function `X`, with the necessary nonvanishing denominators
made explicit.
-/
def positiveEntireDenominatorGaugeOffAxisQuartet_11524 : Prop :=
  ∀ (r θ : ℝ),
    0 < r ∧ r < 1 ∧ 0 < θ ∧ θ < Real.pi / 2 →
      let Aplus : ℂ → ℂ := fun z =>
        1 - 2 * (r : ℂ) * Complex.cos (Real.pi * z - θ) + (r : ℂ) ^ 2
      let Aminus : ℂ → ℂ := fun z =>
        1 - 2 * (r : ℂ) * Complex.cos (Real.pi * z + θ) + (r : ℂ) ^ 2
      let Q : ℂ → ℂ := fun z => Aplus z * Aminus z
      let h : ℝ := Real.log (1 / r) / Real.pi
      Differentiable ℂ Q ∧
        (∀ z : ℂ, Q (-z) = Q z) ∧
        (∀ x : ℝ, (Q (x : ℂ)).im = 0) ∧
        (∀ z : ℂ, Q (z + 2) = Q z) ∧
        (∀ x : ℝ, 0 < (Q (x : ℂ)).re) ∧
        (∀ z : ℂ, Q z = 0 ↔
          (∃ k : ℤ,
            z = (θ / Real.pi : ℂ) + 2 * (k : ℂ) + Complex.I * h ∨
            z = (θ / Real.pi : ℂ) + 2 * (k : ℂ) - Complex.I * h) ∨
          (∃ k : ℤ,
            z = (-θ / Real.pi : ℂ) + 2 * (k : ℂ) + Complex.I * h ∨
            z = (-θ / Real.pi : ℂ) + 2 * (k : ℂ) - Complex.I * h)) ∧
        (∀ (X : ℂ → ℂ) (z : ℂ),
          X z ≠ 0 → X (z + 2) ≠ 0 → Q z ≠ 0 →
          (X (z + 2) * Q (z + 2)) / (X z * Q z) = X (z + 2) / X z)

end
end MathlibPlus.Open.Analysis
