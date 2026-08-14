import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open

noncomputable section

/-- Sign-valued vectors used for the finite exchangeable model. -/
def ProbSignCube (n : ℕ) := {x : Fin n → ℝ // ∀ i, x i = -1 ∨ x i = 1}

/-- Number of plus signs in a sign vector. -/
def plusCount {n : ℕ} (x : ProbSignCube n) : ℕ :=
  (Finset.univ.filter (fun i => x.1 i = 1)).card

/-- The beta integral with integer parameters. -/
def betaIntegral (a b : ℕ) : ℝ :=
  ∫ p in Set.Icc (0 : ℝ) 1, p ^ a * (1 - p) ^ b

/-- Uniform mass for the count K on {0,...,n}. -/
def uniformCountMass (n k : ℕ) : ℝ :=
  if k ≤ n then (1 : ℝ) / (n + 1 : ℝ) else 0

/-- Conditional uniform mass of a sign vector given its plus count. -/
def signMassGivenCount {n : ℕ} (k : ℕ) (x : ProbSignCube n) : ℝ :=
  if plusCount x = k then (1 : ℝ) / (Nat.choose n k : ℝ) else 0

/-- The finite count-mixture mass. -/
def countMixtureMass {n : ℕ} (x : ProbSignCube n) : ℝ :=
  (1 : ℝ) / (n + 1 : ℝ) *
    (1 : ℝ) / (Nat.choose n (plusCount x) : ℝ)

/-- The product-coordinate mass integrated over a uniform P in [0,1]. -/
def integratedProductMass {n : ℕ} (x : ProbSignCube n) : ℝ :=
  ∫ p in Set.Icc (0 : ℝ) 1,
    p ^ (plusCount x) * (1 - p) ^ (n - plusCount x)

/-- The normalized sum of the sign coordinates. -/
def normalizedSignSum {n : ℕ} (x : ProbSignCube n) : ℝ :=
  Finset.sum Finset.univ (fun i : Fin n => x.1 i) / (n : ℝ)

/-- Equal component weights from the source notation p_i = 1/n. -/
def equalComponentWeight (n : ℕ) (_i : Fin n) : ℝ := (1 : ℝ) / n

/-- Claim 46032: the count-uniform and beta-mixture descriptions agree, with
all displayed finite-model identities retained. -/
def claim46032 : Prop :=
  ∀ (n : ℕ), 0 < n →
    (∀ k : ℕ, k ≤ n →
      uniformCountMass n k = (1 : ℝ) / (n + 1 : ℝ)) ∧
    (∀ k : ℕ, k ≤ n → ∀ x : ProbSignCube n,
      signMassGivenCount k x =
        if plusCount x = k then (1 : ℝ) / (Nat.choose n k : ℝ) else 0) ∧
    (∀ x : ProbSignCube n,
      countMixtureMass x =
        uniformCountMass n (plusCount x) * signMassGivenCount (plusCount x) x) ∧
    (∀ k : ℕ, k ≤ n →
      (Nat.choose n k : ℝ) * betaIntegral k (n - k) =
        (1 : ℝ) / (n + 1 : ℝ)) ∧
    (∀ x : ProbSignCube n,
      countMixtureMass x = integratedProductMass x) ∧
    (∀ x : ProbSignCube n,
      normalizedSignSum x =
        (2 * (plusCount x : ℝ) - (n : ℝ)) / (n : ℝ)) ∧
    (∀ i : Fin n, equalComponentWeight n i = (1 : ℝ) / n)

/-- The posterior density obtained from the uniform prior and a plus/minus
likelihood, written without an unnamed probability-law carrier. -/
def posteriorDensity (a b : ℕ) (p : ℝ) : ℝ :=
  if p ∈ Set.Icc (0 : ℝ) 1 then
    p ^ a * (1 - p) ^ b / betaIntegral a b
  else 0

/-- The normalized Beta(a+1,b+1) density. -/
def betaDensity (a b : ℕ) (p : ℝ) : ℝ :=
  if p ∈ Set.Icc (0 : ℝ) 1 then
    ((Nat.factorial (a + b + 1) : ℝ) /
        ((Nat.factorial a : ℝ) * (Nat.factorial b : ℝ))) *
      p ^ a * (1 - p) ^ b
  else 0

/-- Predictive plus probability under the posterior. -/
def posteriorPlusProbability (a b : ℕ) : ℝ :=
  ∫ p in Set.Icc (0 : ℝ) 1, p * betaDensity a b p

/-- The beta-binomial mass of U, the number of pluses among the unrevealed
coordinates. -/
def posteriorUMass (n r a u : ℕ) : ℝ :=
  if u ≤ n - r then
    (Nat.choose (n - r) u : ℝ) *
      betaIntegral (a + u) (r - a + (n - r - u)) /
        betaIntegral a (r - a)
  else 0

/-- Variance of K=a+U under the displayed posterior beta-binomial mass. -/
def posteriorKVariance (n r a : ℕ) : ℝ :=
  let N := n - r
  let μ : ℝ :=
    Finset.sum (Finset.range (N + 1))
      (fun u => ((a + u : ℕ) : ℝ) * posteriorUMass n r a u)
  let μ₂ : ℝ :=
    Finset.sum (Finset.range (N + 1))
      (fun u => ((a + u : ℕ) : ℝ) ^ 2 * posteriorUMass n r a u)
  μ₂ - μ ^ 2

/-- Target variance obtained from the normalized count target. -/
def posteriorTargetVariance (n r a : ℕ) : ℝ :=
  (4 : ℝ) * posteriorKVariance n r a / (n : ℝ) ^ 2

/-- Claim 46033: the posterior, predictive probability, beta-binomial variance,
and normalized target variance have the exact displayed forms. -/
def claim46033 : Prop :=
  ∀ (n r a : ℕ), 0 < n → r ≤ n → a ≤ r →
    (∀ p : ℝ, posteriorDensity a (r - a) p = betaDensity a (r - a) p) ∧
    posteriorPlusProbability a (r - a) =
      (a + 1 : ℝ) / (r + 2 : ℝ) ∧
    posteriorKVariance n r a =
      ((a + 1 : ℝ) * (r - a + 1 : ℝ) * (n - r : ℝ) * (n + 2 : ℝ)) /
        ((r + 2 : ℝ) ^ 2 * (r + 3 : ℝ)) ∧
    posteriorTargetVariance n r a =
      4 * (a + 1 : ℝ) * (r - a + 1 : ℝ) * (n - r : ℝ) * (n + 2 : ℝ) /
        ((n : ℝ) ^ 2 * (r + 2 : ℝ) ^ 2 * (r + 3 : ℝ))

end
end MathlibPlus.Open
