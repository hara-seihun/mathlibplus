import Mathlib

open scoped BigOperators
open MeasureTheory

namespace MathlibPlus.Open.EqualStumpGaussian

noncomputable section

abbrev SignConfig (n : ℕ) := Fin n → Bool

def signValue (b : Bool) : ℝ :=
  if b = true then 1 else -1

def depthOneTreeValue (n : ℕ) (i : Fin n) (x : SignConfig n) : ℝ :=
  signValue (x i)

def fixedMixtureMean (n : ℕ) (x : SignConfig n) : ℝ :=
  (∑ i : Fin n, depthOneTreeValue n i x) / (n : ℝ)

def uniformSignExpectation (n : ℕ) (f : SignConfig n → ℝ) : ℝ :=
  (∑ x : SignConfig n, f x) / (2 : ℝ) ^ n

def fixedOrderTranscript (n : ℕ) (σ : Equiv.Perm (Fin n)) (m : ℕ)
    (x : SignConfig n) : Fin n → Option Bool :=
  fun i =>
    if (σ.symm i).val < m then some (x i) else none

noncomputable def fixedOrderCellVariance (n : ℕ) (σ : Equiv.Perm (Fin n))
    (m : ℕ) (x : SignConfig n) : ℝ :=
  let cell : Finset (SignConfig n) :=
    Finset.univ.filter (fun y =>
      fixedOrderTranscript n σ m y = fixedOrderTranscript n σ m x)
  let cellMean : ℝ :=
    (∑ y ∈ cell, fixedMixtureMean n y) / (cell.card : ℝ)
  (∑ y ∈ cell, (fixedMixtureMean n y - cellMean) ^ 2) / (cell.card : ℝ)

def fixedOrderPosteriorVarianceAt (n : ℕ) (σ : Equiv.Perm (Fin n))
    (m : ℕ) : ℝ :=
  uniformSignExpectation n (fixedOrderCellVariance n σ m)

noncomputable def fixedOrderArea (n : ℕ) (σ : Equiv.Perm (Fin n)) : ℝ :=
  ∑' m : ℕ, fixedOrderPosteriorVarianceAt n σ m

def canonicalMetricSquared (n : ℕ) (x y : SignConfig n) : ℝ :=
  (∑ i : Fin n,
      (depthOneTreeValue n i x - depthOneTreeValue n i y) ^ 2) / (n : ℝ)

def canonicalMetricSquaredByDisagreement (n : ℕ) (x y : SignConfig n) : ℝ :=
  (4 : ℝ) / (n : ℝ) *
    ((Finset.univ.filter (fun i : Fin n => x i ≠ y i)).card : ℝ)

def gaussianDensity (n : ℕ) (g : Fin n → ℝ) : ℝ :=
  ∏ i : Fin n,
    (1 / Real.sqrt (2 * Real.pi)) * Real.exp (-(g i) ^ 2 / 2)

noncomputable def gaussianExpectation (n : ℕ)
    (f : (Fin n → ℝ) → ℝ) : ℝ :=
  ∫ g, f g * gaussianDensity n g ∂
    (Measure.pi (fun _ : Fin n => (volume : Measure ℝ)))

def gaussianProcess (n : ℕ) (x : SignConfig n) (g : Fin n → ℝ) : ℝ :=
  (1 / Real.sqrt (n : ℝ)) * ∑ i : Fin n, g i * signValue (x i)

noncomputable def gaussianSupremum (n : ℕ) (g : Fin n → ℝ) : ℝ :=
  sSup (Set.range (fun x : SignConfig n => gaussianProcess n x g))

noncomputable def gaussianIncrementSupremum (n : ℕ)
    (anchor : SignConfig n) (g : Fin n → ℝ) : ℝ :=
  sSup (Set.range (fun x : SignConfig n =>
    gaussianProcess n x g - gaussianProcess n anchor g))

noncomputable def gaussianSupremumExpectation (n : ℕ) : ℝ :=
  gaussianExpectation n (gaussianSupremum n)

noncomputable def gaussianIncrementSupremumExpectation (n : ℕ)
    (anchor : SignConfig n) : ℝ :=
  gaussianExpectation n (gaussianIncrementSupremum n anchor)

def equalStumpCanonicalWidthObstruction : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    (∀ σ : Equiv.Perm (Fin n),
      (∀ x : SignConfig n, ∀ i : Fin n,
        fixedOrderTranscript n σ n x i = some (x i)) ∧
      (∀ m : ℕ, ∀ x : SignConfig n,
        fixedOrderCellVariance n σ m x =
          ((n - min m n : ℕ) : ℝ) / (n : ℝ) ^ 2) ∧
      fixedOrderArea n σ =
        ((n + 1 : ℕ) : ℝ) / (2 * (n : ℝ)) ∧
      fixedOrderArea n σ ≤ 1) ∧
    (∀ x y : SignConfig n,
      canonicalMetricSquared n x y =
        canonicalMetricSquaredByDisagreement n x y) ∧
    (∀ x y : SignConfig n,
      gaussianExpectation n
        (fun g => (gaussianProcess n x g - gaussianProcess n y g) ^ 2) =
        canonicalMetricSquared n x y) ∧
    gaussianSupremumExpectation n =
      Real.sqrt (2 * (n : ℝ) / Real.pi) ∧
    (∀ anchor : SignConfig n,
      gaussianIncrementSupremumExpectation n anchor =
        Real.sqrt (2 * (n : ℝ) / Real.pi)) ∧
    (∀ C : ℝ, ∃ k : ℕ, 1 ≤ k ∧
      C < Real.sqrt (2 * (k : ℝ) / Real.pi))

end

end MathlibPlus.Open.EqualStumpGaussian
