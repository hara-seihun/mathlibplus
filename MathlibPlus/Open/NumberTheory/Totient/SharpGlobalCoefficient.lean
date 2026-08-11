import Mathlib

/-!
# The sharp global coefficient in the totient bound

Statement-fidelity registry node for admitted claim 667.  The exceptional ninth
primorial is expanded in place, and “least” is represented by attainment of the
bound together with the universal lower-bound property among all valid real
coefficients.
-/

namespace MathlibPlus.Open.NumberTheory.Totient

/-- The coefficient attained uniquely at the ninth primorial is the least real
coefficient in the stated global upper bound for `n / φ(n)` on `n ≥ 3`. -/
def sharpGlobalCoefficient : Prop :=
  let N9 : ℕ := 2 * 3 * 5 * 7 * 11 * 13 * 17 * 19 * 23
  let loglog : ℕ → ℝ := fun n ↦ Real.log (Real.log (n : ℝ))
  let ratio : ℕ → ℝ := fun n ↦ (n : ℝ) / (Nat.totient n : ℝ)
  let Cphi : ℝ :=
    loglog N9 *
      (ratio N9 - Real.exp Real.eulerMascheroniConstant * loglog N9)
  let isGlobalCoefficient : ℝ → Prop := fun D ↦
    ∀ n : ℕ, 3 ≤ n →
      ratio n ≤
        Real.exp Real.eulerMascheroniConstant * loglog n + D / loglog n
  isGlobalCoefficient Cphi ∧
    (∀ D : ℝ, isGlobalCoefficient D → Cphi ≤ D) ∧
    ∀ n : ℕ, 3 ≤ n →
      (ratio n =
          Real.exp Real.eulerMascheroniConstant * loglog n + Cphi / loglog n ↔
        n = N9)

end MathlibPlus.Open.NumberTheory.Totient
