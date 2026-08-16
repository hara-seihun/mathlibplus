import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.FormalizationBatch

/-- Exact finite twisted-trace and phase-invisible Gram-kernel statement. -/
def claim12207 : Prop :=
  let S : Finset ℕ := {3, 5, 7, 11, 13}
  let configurations : Finset (Finset ℕ) := S.powerset
  let trivialPhase : ℕ → ℂ := fun _ => 1
  let characterModFour : ℕ → ℂ := fun p =>
    if p % 2 = 0 then 0
    else if p % 4 = 1 then 1 else -1
  let feature : (ℕ → ℂ) → Finset ℕ → ℕ → ℂ := fun u A p =>
    if p ∈ A then (Real.sqrt (Real.log (p : ℝ)) : ℂ) * u p else 0
  let gram : (ℕ → ℂ) → Finset ℕ → Finset ℕ → ℂ := fun u A B =>
    S.sum (fun p => star (feature u A p) * feature u B p)
  let weightedTrace : (ℕ → ℂ) → ℂ := fun χ =>
    S.sum (fun p =>
      (Real.log (p : ℝ) : ℂ) * χ p *
        (Real.rpow (p : ℝ) (-(1 / 2 : ℝ)) : ℂ))
  (S.card = 5 ∧ configurations.card = 32) ∧
    (∀ A B : Finset ℕ,
      A ∈ configurations → B ∈ configurations →
        gram trivialPhase A B = gram characterModFour A B) ∧
    (∀ c : Finset ℕ → ℂ,
      0 ≤ (configurations.sum (fun A => configurations.sum (fun B =>
        star (c A) * gram trivialPhase A B * c B))).re) ∧
    (∀ u : ℕ → ℂ,
      (∀ p, p ∈ S → ‖u p‖ = 1) →
        ∀ A B : Finset ℕ,
          A ∈ configurations → B ∈ configurations →
            gram u A B = gram trivialPhase A B) ∧
    (weightedTrace trivialPhase ≠ weightedTrace characterModFour) ∧
    |(weightedTrace trivialPhase - weightedTrace characterModFour).re -
          4.1855232649| < 1 / 10 ^ 10

end MathlibPlus.Open.FormalizationBatch
