import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.Batch

/-!
The finite-prime Li coefficient used below is the Taylor coefficient at zero
of the explicitly displayed real Euler product.  The packet's `[u^n]`
notation is represented by `iteratedDeriv n f 0 / n!`.
-/

private noncomputable def finiteEulerProduct (P : Finset ℕ) (s : ℝ) : ℝ :=
  ∏ p ∈ P, (1 - Real.exp (-s * Real.log (p : ℝ)))⁻¹

private noncomputable def finiteEulerLog (P : Finset ℕ) (u : ℝ) : ℝ :=
  Real.log (finiteEulerProduct P (1 / (1 - u)))

private noncomputable def taylorCoefficient (f : ℝ → ℝ) (n : ℕ) : ℝ :=
  iteratedDeriv n f 0 / (Nat.factorial n : ℝ)

private noncomputable def finiteLiCoefficient (P : Finset ℕ) (n : ℕ) : ℝ :=
  (n : ℝ) * taylorCoefficient (finiteEulerLog P) n

/-- Conditional negative type on the additive group of integers. -/
private def conditionalNegativeType (ψ : ℤ → ℝ) : Prop :=
  ∀ c : ℤ →₀ ℝ,
    c.sum (fun _ a => a) = 0 →
      ∑ j ∈ c.support, ∑ k ∈ c.support, c j * c k * ψ (j - k) ≤ 0

private noncomputable def augmentation : ℤ →₀ ℝ :=
  Finsupp.single 0 1 - Finsupp.single 1 1

/-- Claim 10369: the finite-prime Li sequence fails conditional negative type. -/
def finitePrimeLiNotConditionallyNegative : Prop :=
  ∀ P : Finset ℕ, P.Nonempty → (∀ p ∈ P, Nat.Prime p) →
    let ψ : ℤ → ℝ := fun n => finiteLiCoefficient P n.natAbs
    let c : ℤ →₀ ℝ := augmentation
    c.sum (fun _ a => a) = 0 ∧
      (∑ j ∈ c.support, ∑ k ∈ c.support, c j * c k * ψ (j - k) =
        -2 * finiteLiCoefficient P 1) ∧
      0 < -2 * finiteLiCoefficient P 1 ∧
      ¬ conditionalNegativeType ψ

/-- The open upper half-plane. -/
private def upperHalfPlane : Set ℂ := {z | 0 < z.im}

/-- Strict Schur and Herglotz properties on the upper half-plane. -/
private def strictSchurFunction (f : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ f upperHalfPlane ∧
    ∀ z ∈ upperHalfPlane, ‖f z‖ < 1

private def herglotzFunction (f : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ f upperHalfPlane ∧
    ∀ z ∈ upperHalfPlane, 0 < (f z).im

private noncomputable def cayleyTransform (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  Complex.I * (1 + f z) / (1 - f z)

private noncomputable def onePrimeSchurFunction (p : ℕ) (z : ℂ) : ℂ :=
  Complex.ofReal (Real.rpow (p : ℝ) (-(1 : ℝ) / 2)) *
    Complex.exp (Complex.I * z * Complex.ofReal (Real.log (p : ℝ)))

/-- Claim 10372: native one-prime Schur positivity survives. -/
def nativeOnePrimeSchurPositivity : Prop :=
  ∀ p : ℕ, Nat.Prime p →
    strictSchurFunction (onePrimeSchurFunction p) ∧
      herglotzFunction (cayleyTransform (onePrimeSchurFunction p))

private noncomputable def linkedPartitionFunction (ω x y : ℝ) : ℝ :=
  1 + x + y + ω * x * y

private noncomputable def mixedLogCoefficient (ω : ℝ) : ℝ :=
  deriv (fun x : ℝ => deriv (fun y : ℝ =>
    Real.log (linkedPartitionFunction ω x y)) 0) 0

/-- Claim 10473: the mixed coefficient is `ω - 1`, and the prime-power
Euler grammar condition of vanishing mixed coefficient forces `ω = 1`. -/
def linkedPartitionMixedCoefficient : Prop :=
  ∀ ω : ℝ,
    mixedLogCoefficient ω = ω - 1 ∧
      (mixedLogCoefficient ω = 0 → ω = 1)

private noncomputable def centeredLocalWeight (p m : ℕ) : ℝ :=
  Real.rpow (p : ℝ) (-((m : ℝ) / 2))

/-- Claim 10480: a unitary scalar holonomy cannot produce the centered
prime-power weights. -/
def unitaryWilsonHolonomyWrongDecay : Prop :=
  ∀ u : ℂ, ‖u‖ = 1 →
    (∀ m : ℕ, ‖u ^ m‖ = 1) ∧
      ∀ (p m : ℕ), Nat.Prime p → 0 < m →
        ‖(centeredLocalWeight p m : ℂ)‖ < 1 ∧
          u ^ m ≠ (centeredLocalWeight p m : ℂ)

private noncomputable def independencePolynomial {α : Type} [DecidableEq α]
    (M : Matroid α) (E : Finset α) : MvPolynomial α ℤ := by
  classical
  exact ∑ I ∈ E.powerset,
    if M.Indep (I : Set α) then ∏ e ∈ I, MvPolynomial.X e else 0

/-- Claim 10483: the independence polynomial factors exactly when every
subset of the finite ground set is independent. -/
def independencePolynomialCharacterizesFree : Prop :=
  ∀ {α : Type} [DecidableEq α] (M : Matroid α) (E : Finset α),
    (E : Set α) = M.E →
      (independencePolynomial M E = ∏ e ∈ E, (1 + MvPolynomial.X e)) ↔
        ∀ I : Set α, I ⊆ M.E → M.Indep I

end MathlibPlus.Open.ResearchFormalization.Batch
