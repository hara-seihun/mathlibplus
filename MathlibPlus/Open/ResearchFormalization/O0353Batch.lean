import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

noncomputable def eta (α τ : ℝ) : ℂ := (α : ℂ) - Complex.I * (τ : ℂ)

noncomputable def rho (α τ : ℝ) : ℂ := 1 - eta α τ

noncomputable def symmetricQuartet (α τ : ℝ) : Finset ℂ :=
  {eta α τ, star (eta α τ), rho α τ, star (rho α τ)}

noncomputable def primePrefix (Y : ℕ) : Finset ℕ :=
  (Finset.range (Y + 1)).filter Nat.Prime

noncomputable def complexPrimePower (p : ℕ) (s : ℂ) : ℂ :=
  Complex.exp (-(s) * Complex.log (p : ℂ))

noncomputable def shiftedZetaProduct (α τ : ℝ) (Y : ℕ) (s : ℂ) : ℂ :=
  riemannZeta s *
    (symmetricQuartet α τ).prod (fun a => (riemannZeta (s + a))⁻¹) *
    (primePrefix Y).prod (fun p =>
      (symmetricQuartet α τ).prod (fun a =>
        (1 - complexPrimePower p (s + a))⁻¹))

/-- Claim 15585: the explicitly displayed shifted-zeta quartet is symmetric.
The displayed product is the counterfeit product named in the claim. -/
 def claim15585 : Prop :=
  ∃ (α τ : ℝ) (Y₀ : ℕ),
    0 < α ∧ α < (1 : ℝ) / 2 ∧ 0 < τ ∧
      ∀ Y : ℕ, Y₀ ≤ Y →
        (∀ a ∈ symmetricQuartet α τ,
          star a ∈ symmetricQuartet α τ) ∧
        (∀ a ∈ symmetricQuartet α τ,
          1 - a ∈ symmetricQuartet α τ)

noncomputable def shiftedZetaLocalFactor
    (α τ : ℝ) (Y p : ℕ) (s : ℂ) : ℂ :=
  (1 - complexPrimePower p s)⁻¹ *
    (Finset.prod (symmetricQuartet α τ)
      (fun a => 1 - complexPrimePower p (s + a))) *
    (if p ≤ Y then
      Finset.prod (symmetricQuartet α τ)
        (fun a => (1 - complexPrimePower p (s + a))⁻¹)
    else 1)

/-- Claim 15586: the local contribution of the displayed quotient has the
literal finite Euler prefix and the stated tail factor. -/
 def claim15586 : Prop :=
  ∀ (α τ : ℝ) (Y p : ℕ) (s : ℂ),
    0 < α → α < (1 : ℝ) / 2 → 0 < τ → Nat.Prime p → 1 < s.re →
      shiftedZetaLocalFactor α τ Y p s =
        if p ≤ Y then (1 - complexPrimePower p s)⁻¹ else
          (Finset.prod (symmetricQuartet α τ)
            (fun a => 1 - complexPrimePower p (s + a))) /
            (1 - complexPrimePower p s)

noncomputable def localNumerator (α τ : ℝ) (p : ℕ) : Polynomial ℂ :=
  (symmetricQuartet α τ).prod (fun a =>
    1 - Polynomial.C (complexPrimePower p a) * Polynomial.X)

noncomputable def localNumeratorCoeff
    (α τ : ℝ) (p j : ℕ) : ℂ :=
  (localNumerator α τ p).coeff j

noncomputable def localB (α τ : ℝ) (Y p ell : ℕ) : ℂ :=
  if p ≤ Y then 1 else
    (Finset.sum (Finset.range (min ell 4 + 1))
      (fun j => localNumeratorCoeff α τ p j))

noncomputable def globalDirichletCoeff
    (α τ : ℝ) (Y n : ℕ) : ℂ :=
  (Finset.prod (Nat.factorization n).support
    (fun p => localB α τ Y p (Nat.factorization n p)))

noncomputable def localCoeffBound (α τ : ℝ) (p : ℕ) : ℝ :=
  (Finset.sum (Finset.Icc 1 4)
    (fun j => ‖localNumeratorCoeff α τ p j‖))

noncomputable def claimedLocalCoeffBound (α : ℝ) (p : ℕ) : ℝ :=
  (1 + Real.rpow (p : ℝ) (-α)) ^ 2 *
      (1 + Real.rpow (p : ℝ) (-(1 - α))) ^ 2 - 1

/-- Claim 15587: the local numerator coefficients, local positivity and
uniform convergence, and the resulting multiplicative (not completely
multiplicative) global coefficients. -/
 def claim15587 : Prop :=
  ∀ (α τ : ℝ), 0 < α → α < (1 : ℝ) / 2 → 0 < τ →
    ∃ Y₀ : ℕ, ∀ Y : ℕ, Y₀ ≤ Y →
      (∀ p : ℕ, Nat.Prime p → Y < p →
        localCoeffBound α τ p ≤ claimedLocalCoeffBound α p) ∧
      (∀ p ell : ℕ, Nat.Prime p → Y < p →
        (localB α τ Y p ell).im = 0 ∧ 0 < (localB α τ Y p ell).re) ∧
      (∀ ε : ℝ, 0 < ε → ∃ Y₁ : ℕ, ∀ Y : ℕ, Y₁ ≤ Y →
        ∀ p ell : ℕ, Nat.Prime p → Y < p →
          ‖localB α τ Y p ell - 1‖ < ε) ∧
      (∀ ε : ℝ, 0 < ε → ∃ Y₁ : ℕ, ∀ Y : ℕ, Y₁ ≤ Y →
        ∀ p : ℕ, Nat.Prime p → Y < p →
          localCoeffBound α τ p < ε) ∧
      (∀ n : ℕ, 0 < n →
        (globalDirichletCoeff α τ Y n).im = 0 ∧
          0 < (globalDirichletCoeff α τ Y n).re) ∧
      (∀ m n : ℕ, 0 < m → 0 < n → Nat.Coprime m n →
        globalDirichletCoeff α τ Y (m * n) =
          globalDirichletCoeff α τ Y m * globalDirichletCoeff α τ Y n) ∧
      (∃ m n : ℕ, 0 < m ∧ 0 < n ∧
        globalDirichletCoeff α τ Y (m * n) ≠
          globalDirichletCoeff α τ Y m * globalDirichletCoeff α τ Y n)

noncomputable def zetaMultiplier (α τ : ℝ) (p k : ℕ) : ℝ :=
  1 - 2 *
      (Real.rpow (p : ℝ) (-(k : ℝ) * α) +
        Real.rpow (p : ℝ) (-(k : ℝ) * (1 - α))) *
      Real.cos ((k : ℝ) * τ * Real.log (p : ℝ))

noncomputable def lambdaZero (α τ : ℝ) (Y p k : ℕ) : ℝ :=
  if h : Nat.Prime p ∧ 0 < k then
    Real.log (p : ℝ) * if p ≤ Y then 1 else zetaMultiplier α τ p k
  else 0

/-- Claim 15588: the uncorrected generalized von Mangoldt formula, positivity,
and uniform convergence of its prime-power multipliers. -/
 def claim15588 : Prop :=
  ∀ (α τ : ℝ), 0 < α → α < (1 : ℝ) / 2 → 0 < τ →
    (∃ Y₀ : ℕ, ∀ Y : ℕ, Y₀ ≤ Y →
      (∀ p k : ℕ, Nat.Prime p → 0 < k →
        lambdaZero α τ Y p k / Real.log (p : ℝ) =
          if p ≤ Y then 1 else zetaMultiplier α τ p k) ∧
      (∀ p k : ℕ, Nat.Prime p → 0 < k → 0 < lambdaZero α τ Y p k) ∧
      (∀ ε : ℝ, 0 < ε → ∃ Y₁ : ℕ, ∀ Y : ℕ, Y₁ ≤ Y →
        ∀ p k : ℕ, Nat.Prime p → 0 < k → Y < p →
          |zetaMultiplier α τ p k - 1| < ε))

noncomputable def weightedPerturbationTerm
    (α τ : ℝ) (Y p k : ℕ) : ℝ :=
  if h : Nat.Prime p ∧ 0 < k ∧ Y < p then
    (lambdaZero α τ Y p k - Real.log (p : ℝ)) / (p : ℝ) ^ k
  else 0

noncomputable def weightedPerturbation (α τ : ℝ) (Y : ℕ) : ℝ :=
  ∑' q : ℕ × ℕ, weightedPerturbationTerm α τ Y q.1 q.2

/-- Claim 15589: the weighted perturbation is absolutely summable and has the
stated power-size bound. -/
 def claim15589 : Prop :=
  ∀ (α τ : ℝ), 0 < α → α < (1 : ℝ) / 2 → 0 < τ →
    (∀ Y : ℕ,
      Summable (fun q : ℕ × ℕ =>
        |weightedPerturbationTerm α τ Y q.1 q.2|)) ∧
    ∃ (C : ℝ) (Y₀ : ℕ), 0 ≤ C ∧
      ∀ Y : ℕ, Y₀ ≤ Y →
        |weightedPerturbation α τ Y| ≤
          C * Real.rpow (Y : ℝ) (-α)

noncomputable def correctionPrimes (Y : ℕ) : Finset ℕ :=
  (Finset.Icc (Y + 1) (2 * Y)).filter Nat.Prime

noncomputable def correctionMass (Y : ℕ) (u : ℝ) : ℝ :=
  -∑' p : ℕ,
    if h : Nat.Prime p ∧ Y < p ∧ p ≤ 2 * Y then
      Real.log (p : ℝ) * u / ((p : ℝ) - u)
    else 0

noncomputable def correctionDerivativeAtZero (Y : ℕ) : ℝ :=
  -∑' p : ℕ,
    if h : Nat.Prime p ∧ Y < p ∧ p ≤ 2 * Y then
      Real.log (p : ℝ) / (p : ℝ)
    else 0

noncomputable def correctionProduct (Y : ℕ) (u : ℝ) (s : ℂ) : ℂ :=
  (correctionPrimes Y).prod (fun p =>
    1 - (u : ℂ) * complexPrimePower p s)

noncomputable def correctedZetaProduct
    (α τ : ℝ) (Y : ℕ) (u : ℝ) (s : ℂ) : ℂ :=
  shiftedZetaProduct α τ Y s * correctionProduct Y u s

/-- Claim 15590: the finite correction has the displayed weighted mass,
limiting derivative, and an eventually small exact zero. -/
 def claim15590 : Prop :=
  ∀ (α τ : ℝ), 0 < α → α < (1 : ℝ) / 2 → 0 < τ →
    (∀ Y : ℕ,
      HasDerivAt (correctionMass Y) (correctionDerivativeAtZero Y) 0) ∧
    (Filter.Tendsto correctionDerivativeAtZero Filter.atTop
      (nhds (-Real.log 2))) ∧
    (∃ (u : ℕ → ℝ) (C : ℝ) (Y₀ : ℕ), 0 ≤ C ∧
      ∀ Y : ℕ, Y₀ ≤ Y →
        |u Y| ≤ C * Real.rpow (Y : ℝ) (-α) ∧
        weightedPerturbation α τ Y + correctionMass Y (u Y) = 0)

noncomputable def correctedZetaMultiplier
    (α τ : ℝ) (Y : ℕ) (u : ℝ) (p k : ℕ) : ℝ :=
  if p ≤ Y then 1 else
    if Y < p ∧ p ≤ 2 * Y then
      zetaMultiplier α τ p k - u ^ k
    else zetaMultiplier α τ p k

noncomputable def correctedLambdaZero
    (α τ : ℝ) (Y : ℕ) (u : ℝ) (p k : ℕ) : ℝ :=
  if h : Nat.Prime p ∧ 0 < k then
    Real.log (p : ℝ) * correctedZetaMultiplier α τ Y u p k
  else 0

noncomputable def correctedLocalB
    (α τ : ℝ) (Y : ℕ) (u : ℝ) (p ell : ℕ) : ℂ :=
  if p ≤ Y then 1 else
    if Y < p ∧ p ≤ 2 * Y then
      if ell = 0 then 1
      else localB α τ Y p ell - (u : ℂ) * localB α τ Y p (ell - 1)
    else localB α τ Y p ell

noncomputable def correctedGlobalDirichletCoeff
    (α τ : ℝ) (Y : ℕ) (u : ℝ) (n : ℕ) : ℂ :=
  Finset.prod (Nat.factorization n).support
    (fun p => correctedLocalB α τ Y u p (Nat.factorization n p))

/-- Claim 15591: the correction changes the displayed local multipliers and
coefficients, while preserving strict positivity for the selected small
correction. -/
 def claim15591 : Prop :=
  ∀ (α τ : ℝ), 0 < α → α < (1 : ℝ) / 2 → 0 < τ →
    ∃ (u : ℕ → ℝ) (C : ℝ) (Y₀ : ℕ), 0 ≤ C ∧
      ∀ Y : ℕ, Y₀ ≤ Y →
        |u Y| ≤ C * Real.rpow (Y : ℝ) (-α) ∧
        weightedPerturbation α τ Y + correctionMass Y (u Y) = 0 ∧
        (∀ p k : ℕ, Nat.Prime p → 0 < k →
          0 < correctedLambdaZero α τ Y (u Y) p k) ∧
        (∀ p ell : ℕ, Nat.Prime p →
          (correctedLocalB α τ Y (u Y) p ell).im = 0 ∧
          0 < (correctedLocalB α τ Y (u Y) p ell).re) ∧
        (∀ p ell : ℕ, Nat.Prime p → Y < p → p ≤ 2 * Y → 0 < ell →
          correctedLocalB α τ Y (u Y) p ell =
            localB α τ Y p ell - (u Y : ℂ) * localB α τ Y p (ell - 1)) ∧
        (∀ n : ℕ, 0 < n →
          (correctedGlobalDirichletCoeff α τ Y (u Y) n).im = 0 ∧
            0 < (correctedGlobalDirichletCoeff α τ Y (u Y) n).re)

end MathlibPlus.Open.ResearchFormalization
