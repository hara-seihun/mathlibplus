import Mathlib

namespace MathlibPlus.Analysis

/--
The root-evaluation identity from admitted claim 4806.  The family `P` is
constructed by the source's exact Charlier recurrence with `a = 5 / 4`, so
this statement introduces no arbitrary replacement family.
-/
theorem rootEvaluationRecurrence_claim4806 :
    let P : ℕ → Polynomial ℝ := fun k =>
      Nat.rec 1
        (fun _ p => Polynomial.X * p.derivative +
          (Polynomial.C (5 / 4 : ℝ) - Polynomial.X) * p) k
    ∀ (k : ℕ) (ρ : ℝ), 0 < ρ →
      Polynomial.eval ρ (P k) = 0 →
        Polynomial.eval ρ (P (k + 1)) =
          ρ * Polynomial.eval ρ (P k).derivative := by
  dsimp
  intro k ρ _hρ hzero
  simp [hzero]

end MathlibPlus.Analysis
