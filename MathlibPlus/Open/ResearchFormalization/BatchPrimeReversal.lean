import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization

noncomputable def primeLogarithmicTileLength (p : ℕ) : ℝ := Real.log p

noncomputable def primeActivity (p : ℕ) (z : ℂ) : ℂ :=
  Complex.exp (-z * (Real.log (p : ℝ) : ℂ))

noncomputable def reversalActivity (q : ℂ) : ℂ := q⁻¹

noncomputable def laurentEvaluation (P : ℤ →₀ ℂ) (q : ℂ) : ℂ :=
  Finset.sum P.support (fun k => P k * q ^ k)

def reciprocalLaurent (P : ℤ →₀ ℂ) (d : ℤ) : Prop :=
  ∀ k : ℤ, P k = P (d - k)

noncomputable def palindromicDefect : ℤ →₀ ℂ :=
  Finsupp.single (-1 : ℤ) (1 : ℂ) +
    Finsupp.single (0 : ℤ) (-3 : ℂ) +
      Finsupp.single (1 : ℤ) (1 : ℂ)

def primeActivityAndReversalSymmetryClaim : Prop :=
  (∀ p : ℕ, Nat.Prime p →
    primeLogarithmicTileLength p = Real.log (p : ℝ) ∧
    ∀ z : ℂ,
      primeActivity p z = Complex.exp (-z * (Real.log (p : ℝ) : ℂ))) ∧
  (∀ q : ℂ, q ≠ 0 → reversalActivity q = q⁻¹) ∧
  (∀ P : ℤ →₀ ℂ, ∀ d : ℤ, reciprocalLaurent P d → ∀ q : ℂ, q ≠ 0 →
    laurentEvaluation P (q⁻¹) = q ^ (-d) * laurentEvaluation P q ∧
    (laurentEvaluation P q = 0 → laurentEvaluation P (q⁻¹) = 0)) ∧
  (∃ q : ℂ,
    q ≠ 0 ∧ reciprocalLaurent palindromicDefect 0 ∧
      laurentEvaluation palindromicDefect q = 0 ∧ ‖q‖ ≠ 1)

end MathlibPlus.Open.ResearchFormalization
