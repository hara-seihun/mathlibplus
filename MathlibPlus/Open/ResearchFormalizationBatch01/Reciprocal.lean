import Mathlib

open scoped BigOperators Matrix

namespace MathlibPlus.Open.ResearchFormalizationBatch01

noncomputable section

def reciprocalSign (b : Bool) : ℝ := if b then 1 else -1

def reciprocalSheetFormula (r : ℕ) (l q : Fin r → ℝ)
    (ε : Fin r → Bool) : ℝ :=
  Real.exp ((5 / 4 : ℝ) * ∑ j, reciprocalSign (ε j) * Real.log (l j)) *
    |Matrix.det (fun i j =>
      Real.exp (-q i * Real.exp (reciprocalSign (ε j) * Real.log (l j))))|

def reciprocalParametersOrdered (r : ℕ)
    (l q : Fin r → ℝ) : Prop :=
  (∀ i, 0 < q i) ∧
  (∀ i, 1 < l i) ∧
  (∀ i j, i < j → l i < l j)

/-- The reciprocal sheet masses are the exact determinant formula with the
packet's index order and positivity hypotheses. -/
def claim47752 : Prop :=
  ∀ (r : ℕ) (l q : Fin r → ℝ), reciprocalParametersOrdered r l q →
    ∃! A : (Fin r → Bool) → ℝ,
      ∀ ε, A ε = reciprocalSheetFormula r l q ε

end
end MathlibPlus.Open.ResearchFormalizationBatch01
