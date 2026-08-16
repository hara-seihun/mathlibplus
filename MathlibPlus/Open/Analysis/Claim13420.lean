import Mathlib

namespace MathlibPlus.Open.Analysis.Claim13420

noncomputable section

/-- The prime cut-off used by the finite Euler product and finite prime sum. -/
def primeCutoff (y : ℕ) : Finset ℕ :=
  (Finset.range (y + 1)).filter Nat.Prime

/-- The complex term denoted by `p ^ (-z)` in the admitted statement. -/
def primePower (p : ℕ) (z : ℂ) : ℂ :=
  Complex.exp (-z * (Real.log (p : ℝ) : ℂ))

/-- `A_y(z) = ∏_{p ≤ y} (1 - p^(-z))`. -/
def finiteEulerProduct (y : ℕ) (z : ℂ) : ℂ :=
  Finset.prod (primeCutoff y) (fun p => 1 - primePower p z)

/-- `P_y(z) = ∑_{p ≤ y} p^(-z)`. -/
def primeSum (y : ℕ) (z : ℂ) : ℂ :=
  Finset.sum (primeCutoff y) (fun p => primePower p z)

/--
For `σ > 1/2`, the finite Euler-product logarithm has the admitted
first-prime decomposition, with a bound independent of `t` and `y`.
-/
def firstPrimeLogarithmDecomposition : Prop :=
  ∀ σ : ℝ, (1 / 2 : ℝ) < σ →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (y : ℕ) (t : ℝ),
        |Real.log ‖finiteEulerProduct y ((σ : ℂ) + (t : ℂ) * Complex.I)‖ +
            (primeSum y ((σ : ℂ) + (t : ℂ) * Complex.I)).re| ≤ C

end
end MathlibPlus.Open.Analysis.Claim13420
