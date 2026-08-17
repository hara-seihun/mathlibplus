import MathlibPlus.Open.ResearchFormalization.AdmittedBatch11413_11414_11424_11427

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization

/-- Critical-line Mellin--Plancherel identity for the primorial Nyman defect. -/
def claim11425 : Prop :=
  let primeSet : ℕ → Finset ℕ := fun y =>
    Finset.filter Nat.Prime (Finset.Icc 2 y)
  let Q : ℕ → ℕ := fun y =>
    ∏ p ∈ primeSet y, p
  let A : ℕ → ℂ → ℂ := fun y s =>
    ∑ d ∈ Nat.divisors (Q y),
      ((ArithmeticFunction.moebius d : ℤ) : ℂ) *
        Complex.cpow (d : ℂ) (-s)
  let a : ℕ → ℝ := fun y =>
    ∑ d ∈ Nat.divisors (Q y),
      ((ArithmeticFunction.moebius d : ℤ) : ℝ) / (d : ℝ)
  let b : ℝ → ℝ → ℝ := fun α x =>
    Int.fract (α / x) - α * Int.fract (1 / x)
  let v : ℕ → ℝ → ℝ := fun y x =>
    -∑ d ∈ Nat.divisors (Q y),
      ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
        b (1 / (d : ℝ)) x
  let g : ℕ → ℝ → ℝ := fun y x => 1 - v y x
  let normSq : ℕ → ℝ := fun y =>
    ∫ x in Set.Ioo (0 : ℝ) 1, (g y x) ^ 2
  ∀ y : ℕ,
    normSq y =
      (2 * Real.pi)⁻¹ *
        ∫ t : ℝ,
          ‖(1 : ℂ) -
              riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) *
                (A y ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) -
                  (a y : ℂ))‖ ^ 2 /
            (1 / 4 + t ^ 2)

end MathlibPlus.Open.ResearchFormalization
