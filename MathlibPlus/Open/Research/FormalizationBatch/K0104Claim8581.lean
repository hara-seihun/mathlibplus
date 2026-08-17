import MathlibPlus.Combinatorics.PullFirstClaim8569

namespace MathlibPlus.Open.Research.FormalizationBatch.K0104Claim8581

open scoped BigOperators Interval
open MathlibPlus.Combinatorics.Claim8569

noncomputable section

/-- The node polynomial attached to the ordered Gaussian nodes. -/
def nodePolynomial8581 {n : ℕ} (x : Fin n → ℝ) : Polynomial ℝ :=
  ∏ i : Fin n, (Polynomial.X - Polynomial.C (x i))

/-- The dual complement weight at a node. -/
def dualHoleWeight8581 {n : ℕ}
    (x w : Fin n → ℝ) (i : Fin n) : ℝ :=
  1 / (w i *
    ((Polynomial.derivative (nodePolynomial8581 x)).eval (x i)) ^ 2)

/-- The finite carrier of m-element hole sets. -/
def holeSets8581 (n m : ℕ) : Finset (Finset (Fin n)) :=
  (Finset.univ : Finset (Finset (Fin n))).filter (fun H => H.card = m)

/-- The unnormalised mass of a hole set for node weights u. -/
def holeMass8581 {n : ℕ}
    (x u : Fin n → ℝ) (H : Finset (Fin n)) : ℝ :=
  vandermondeOn x H ^ 2 * H.prod u

/-- The probability mass of a hole set in the m-hole ensemble. -/
def holeProbability8581 {n m : ℕ}
    (x u : Fin n → ℝ) (H : Finset (Fin n)) : ℝ :=
  holeMass8581 x u H / partitionFunction n m x u

/-- The logarithmic node statistic of a hole set. -/
def logarithmicHoleStatistic8581 {n : ℕ}
    (x : Fin n → ℝ) (H : Finset (Fin n)) : ℝ :=
  H.sum (fun i => Real.log (x i))

/-- The interpolated dual node weight at time t. -/
def interpolatedHoleWeight8581 {n : ℕ}
    (x w : Fin n → ℝ) (t : ℝ) (i : Fin n) : ℝ :=
  dualHoleWeight8581 x w i * Real.rpow (x i) (-t)

/-- The interpolated logarithmic expectation over the exact m-hole carrier. -/
def interpolatedLogExpectation8581 {n m : ℕ}
    (x w : Fin n → ℝ) (t : ℝ) : ℝ :=
  (holeSets8581 n m).sum (fun H =>
    holeProbability8581 (m := m) x
        (interpolatedHoleWeight8581 x w t) H *
      logarithmicHoleStatistic8581 x H)

/-- The inverse-product partition ratio. -/
def inverseProductRatio8581 {n m : ℕ}
    (x w : Fin n → ℝ) : ℝ :=
  partitionFunction n m x
      (fun i => dualHoleWeight8581 x w i / x i) /
    partitionFunction n m x (fun i => dualHoleWeight8581 x w i)

/-- The logarithmic integral representation of the inverse-product ratio. -/
def integralRepresentationOfInverseProductRatio_claim8581 : Prop :=
  ∀ (n m : ℕ) (x w : Fin n → ℝ),
    m ≤ n →
    StrictMono x →
    (∀ i : Fin n, 0 < x i) →
    (∀ i : Fin n, 0 < w i) →
    Real.log (inverseProductRatio8581 (m := m) x w) =
      -∫ t in (0 : ℝ)..1,
        interpolatedLogExpectation8581 (m := m) x w t

end

end MathlibPlus.Open.Research.FormalizationBatch.K0104Claim8581
