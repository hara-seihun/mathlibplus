import Mathlib

namespace MathlibPlus.Open.Research.SelbergCoefficientwiseInverse

noncomputable section

/-- The constant-one arithmetic function convolved with itself, written `d = 1 * 1`
    in the admitted coefficientwise statement.  Here `ArithmeticFunction.zeta` is
    the constant-one arithmetic function on positive integers, not the convolution
    identity. -/
private def divisorKernel15219 : ArithmeticFunction ℝ :=
  (ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
    (ArithmeticFunction.zeta : ArithmeticFunction ℝ)

/-- The square of the Möbius convolution inverse of the divisor kernel. -/
private def mobiusSquare15219 : ArithmeticFunction ℝ :=
  (ArithmeticFunction.moebius : ArithmeticFunction ℝ) *
    (ArithmeticFunction.moebius : ArithmeticFunction ℝ)

/-- The linearized Selberg operator at the von Mangoldt arithmetic function. -/
private def linearizedSelberg15219 (h : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n =>
    h n * Real.log (n : ℝ) +
      2 * ((ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) * h) n,
    by simp⟩

/-- The displayed coefficientwise right-hand side transform `g`. -/
private def coefficientwiseG15219
    (r : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n =>
    if n = 1 then 0
    else (divisorKernel15219 * r) n / Real.log (n : ℝ),
    by simp⟩

/-- The coefficientwise candidate `m₂ * g` for a right-hand side `r`. -/
private def coefficientwiseCandidate15219
    (r : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  mobiusSquare15219 * coefficientwiseG15219 r

/-- The displayed `g` is a prefix-causal function of its literal right-hand side. -/
private def prefixCausal15219 : Prop :=
  ∀ (N : ℕ) (r₁ r₂ : ArithmeticFunction ℝ),
    (∀ n, n ≤ N → r₁ n = r₂ n) →
      ∀ n, n ≤ N →
        coefficientwiseCandidate15219 r₁ n =
          coefficientwiseCandidate15219 r₂ n

/-- No nonzero normalized perturbation survives the finite-prefix homogeneous
    linearized equation, i.e. the inverse exposes no new literal perturbation
    orbit. -/
private def noLiteralPerturbationOrbit15219 : Prop :=
  ∀ (N : ℕ) (δ : ArithmeticFunction ℝ),
    δ 1 = 0 →
      (∀ n, 2 ≤ n → n ≤ N → linearizedSelberg15219 δ n = 0) →
        ∀ n, n ≤ N → δ n = 0

/-- Exact coefficientwise inverse from admitted claim 15219.

The right-hand side and perturbation carriers are normalized by their value at
`1`, as in the causal derivative carrier: the operator has zero coefficient at
`1`, while the displayed `g` also starts with `g 1 = 0`.  The statement asserts
both the all-coefficient recovery and its finite-prefix/no-orbit consequences. -/
def exactCoefficientwiseInverse15219 : Prop :=
  (∀ r : ArithmeticFunction ℝ, r 1 = 0 →
    (∃! h : ArithmeticFunction ℝ,
      h 1 = 0 ∧ linearizedSelberg15219 h = r) ∧
      coefficientwiseCandidate15219 r 1 = 0 ∧
      linearizedSelberg15219 (coefficientwiseCandidate15219 r) = r ∧
      (∀ h : ArithmeticFunction ℝ,
        h 1 = 0 → linearizedSelberg15219 h = r →
          h = coefficientwiseCandidate15219 r)) ∧
  prefixCausal15219 ∧
  noLiteralPerturbationOrbit15219

end

end MathlibPlus.Open.Research.SelbergCoefficientwiseInverse
