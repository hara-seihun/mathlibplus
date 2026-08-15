import Mathlib

namespace MathlibPlus.Open.Analysis

/--
One-root reflection of a zero across the critical circle.  The hypotheses
place the zero strictly inside the circle and the singular-inner coordinate
on the critical line; the displayed quotient is the division by the inner
factor from the admitted claim.
-/
def oneRootCriticalCircleReflection : Prop :=
  ∀ (q : ℕ) (z α : ℂ) (t : ℝ),
    2 ≤ q →
    0 < ‖α‖ →
    ‖α‖ < (q : ℝ) ^ (-1 / 2 : ℝ) →
    let L : ℝ := Real.log (q : ℝ)
    let r : ℝ := (q : ℝ) ^ (-1 / 2 : ℝ)
    let s : ℂ := 1 / (1 - z)
    let Φq : ℂ := Complex.exp ((L : ℂ) * ((1 : ℂ) / 2 - s))
    let a : ℂ := α / (r : ℂ)
    let w : ℂ := (r : ℂ) * Φq
    let b : ℂ := (Φq - a) / (1 - star a * Φq)
    let αstar : ℂ := (r : ℂ) ^ 2 / star α
    let reflected : ℂ → ℂ :=
      fun x => (r : ℂ) * (1 - star α * x / (r : ℂ) ^ 2)
    s = (1 : ℂ) / 2 + (t : ℂ) * Complex.I →
      (w - α) / b = reflected w ∧
      (∀ x : ℂ, reflected x = 0 ↔ x = αstar) ∧
      ‖αstar‖ > r

end MathlibPlus.Open.Analysis
