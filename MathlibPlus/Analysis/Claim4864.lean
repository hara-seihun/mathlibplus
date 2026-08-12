import Mathlib.Data.Complex.BigOperators
import Mathlib.Tactic

open scoped BigOperators ComplexConjugate

namespace MathlibPlus.Analysis.FiniteWeilPositivity

/-- Claim 4864: when every occurrence in a finite reflected packet is fixed by
`τ(s) = 1 - conj s`, the real reflection form is the sum of squared moduli. -/
theorem criticalFixed_finiteWeil_sumSquares_claim4864
    {n : ℕ} (roots : Fin n → ℂ) (F : ℂ → ℂ)
    (hfixed : ∀ i, 1 - conj (roots i) = roots i) :
    (∑ i, (F (roots i) * conj (F (1 - conj (roots i)))).re) =
      ∑ i, Complex.normSq (F (roots i)) := by
  simp_rw [hfixed]
  simp_rw [Complex.mul_conj]
  simp

end MathlibPlus.Analysis.FiniteWeilPositivity
