import Mathlib

open Filter
open scoped Topology

namespace MathlibPlus.NumberTheory.Claim8254

/-- The generalized-Jordan coefficient from the admitted supporting statement. -/
noncomputable def generalizedJordanCoefficient (q : ℕ) (t : ℝ) (n : ℕ) : ℝ :=
  Finset.prod (n.primeFactors.filter (fun p => p ≠ q))
    (fun p => 1 - Real.rpow (p : ℝ) (-t))

/-- The summatory function from the admitted supporting statement. -/
noncomputable def generalizedJordanSummatory (q : ℕ) (t x : ℝ) : ℝ :=
  Finset.sum (Finset.Icc 1 (Nat.floor x))
    (fun n => generalizedJordanCoefficient q t n)

/-- The density constant from the admitted supporting statement. -/
noncomputable def generalizedJordanDensity (q : ℕ) (t : ℝ) : ℝ :=
  if 0 < t then
    1 / (Complex.re (riemannZeta (1 + (t : ℂ))) *
      (1 - Real.rpow (q : ℝ) (-1 - t)))
  else 0

/-- Uniform generalized-Jordan summatory discrepancy. -/
def uniformGeneralizedJordanSummatoryDiscrepancy_claim8254 : Prop :=
  ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧
    ∀ q : ℕ, Nat.Prime q →
      ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        ∀ x : ℝ, 2 ≤ x →
          |generalizedJordanSummatory q t x -
              generalizedJordanDensity q t * x| ≤
            C * x * Real.exp (-κ * Real.sqrt (Real.log (2 * x)))

end MathlibPlus.NumberTheory.Claim8254
