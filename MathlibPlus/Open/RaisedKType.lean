import Mathlib

/-!
# Raised K-type asymptotics

Open registry statements for the attenuation of raised local factors.
-/

open scoped BigOperators

namespace MathlibPlus.Open.RaisedKType

/-- Uniformly for natural representation indices `m` bounded by a fixed
multiple of `√t`, the positive attenuation factor differs from one by
`O(t⁻¹)` as `t → +∞`.

The constants `M` and `C` expose the uniform meaning of the source phrase
`m = O(√t)`: for every fixed scale bound `M`, one error constant works for all
indices in that range. -/
def attenuationAsymptoticallyNegligible : Prop :=
  let rho : ℝ → ℕ → ℝ → ℝ := fun k m t =>
    Real.sqrt <| ∏ r ∈ Finset.range m,
      (((k + 2 * (r : ℝ) + 1 / 2) ^ 2 + t ^ 2) /
        ((k + 2 * (r : ℝ) + 3 / 2) ^ 2 + t ^ 2))
  ∀ k > 0, ∀ M ≥ 0, ∃ C ≥ 0, ∃ T ≥ 1,
    ∀ t ≥ T, ∀ m : ℕ,
      (m : ℝ) ≤ M * Real.sqrt t →
        |rho k m t - 1| ≤ C / t

end MathlibPlus.Open.RaisedKType
