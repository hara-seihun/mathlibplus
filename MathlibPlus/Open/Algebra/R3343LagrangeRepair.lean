import MathlibPlus.Open.Algebra.LagrangeProductIdentity

noncomputable section

namespace MathlibPlus.Open.Algebra.R3343LagrangeRepair

abbrev NodePolynomial472 := Polynomial ℝ

def nodePolynomial472 (n : ℕ) (t : Fin n → ℝ) : NodePolynomial472 :=
  ∏ i : Fin n, (Polynomial.X - Polynomial.C (t i))

def lagrangeFactor472 (n : ℕ) (t : Fin n → ℝ)
    (i : Fin n) (x : ℝ) : ℝ :=
  (nodePolynomial472 n t).eval x /
    ((nodePolynomial472 n t).derivative.eval (t i) * (x - t i))

def vandermonde472 (n : ℕ) (t : Fin n → ℝ) : ℝ :=
  ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, |t j - t i|

def lebesgueFunction472 (n : ℕ) (t : Fin n → ℝ) (x : ℝ) : ℝ :=
  ∑ i : Fin n, |lagrangeFactor472 n t i x|

def nodeHypotheses472 (n : ℕ) (t : Fin n → ℝ) : Prop :=
  1 ≤ n ∧
    (∀ i j, i ≠ j → t i ≠ t j) ∧
    (∀ i, t i ∈ Set.Icc (-1 : ℝ) 1)

def nonnode472 (n : ℕ) (t : Fin n → ℝ) (x : ℝ) : Prop :=
  ∀ i : Fin n, x ≠ t i

/-- Claim 47246: the pointwise arithmetic-geometric-mean bound for the
Lebesgue function on the exact node carrier of claim 47245. -/
def claim47246 : Prop :=
  ∀ (n : ℕ) (t : Fin n → ℝ),
    nodeHypotheses472 n t →
    ∀ x : ℝ, nonnode472 n t x →
      (lebesgueFunction472 n t x) ^ n ≥
        (n : ℝ) ^ n *
          |(nodePolynomial472 n t).eval x| ^ (n - 1) /
            (vandermonde472 n t) ^ 2

def logarithmicMean472 (A : Set ℝ) (f : ℝ → ℝ) : ℝ :=
  ((MeasureTheory.volume A).toReal)⁻¹ * ∫ x in A, f x

/-- Claim 47247: the measurable finite-positive-set logarithmic consequence
of the pointwise Lebesgue bound. -/
def claim47247 : Prop :=
  ∀ (n : ℕ) (t : Fin n → ℝ),
    nodeHypotheses472 n t →
    ∀ A : Set ℝ, ∀ B : ℝ,
      MeasurableSet A →
      A ⊆ Set.Icc (-1 : ℝ) 1 →
      0 < (MeasureTheory.volume A).toReal →
      MeasureTheory.volume A ≠ ⊤ →
      (∀ᵐ x ∂MeasureTheory.volume.restrict A,
        lebesgueFunction472 n t x ≤ B) →
      Real.exp
          (logarithmicMean472 A
            (fun x => Real.log |(nodePolynomial472 n t).eval x|)) ≤
        (vandermonde472 n t) ^ ((2 : ℝ) / (n - 1)) *
          (B / (n : ℝ)) ^ ((n : ℝ) / (n - 1))

def prefixPolynomial472 (t : ℕ → ℝ) (m : ℕ) : NodePolynomial472 :=
  ∏ i : Fin m, (Polynomial.X - Polynomial.C (t i.1))

def prefixLagrangeFactor472 (t : ℕ → ℝ) (m : ℕ)
    (i : Fin m) (x : ℝ) : ℝ :=
  (prefixPolynomial472 t m).eval x /
    ((prefixPolynomial472 t m).derivative.eval (t i.1) *
      (x - t i.1))

def prefixVandermonde472 (t : ℕ → ℝ) (m : ℕ) : ℝ :=
  ∏ i : Fin m, ∏ j ∈ Finset.Ioi i,
    |t j.1 - t i.1|

def prefixLebesgue472 (t : ℕ → ℝ) (m : ℕ) (x : ℝ) : ℝ :=
  ∑ i : Fin m, |prefixLagrangeFactor472 t m i x|

def prefixNodesDistinct472 (t : ℕ → ℝ) (N : ℕ) : Prop :=
  ∀ i j : Fin N, i ≠ j → t i.1 ≠ t j.1

def prefixNodesInInterval472 (t : ℕ → ℝ) (N : ℕ) : Prop :=
  ∀ i : Fin N, t i.1 ∈ Set.Icc (-1 : ℝ) 1

def productPrefixPolynomial472 (t : ℕ → ℝ) (n : ℕ) : NodePolynomial472 :=
  ∏ m ∈ Finset.Ico n (2 * n), prefixPolynomial472 t m

/-- Claim 47250: insertion at the next node, the fixed-point bounded-Lebesgue
product inequality, and the resulting monic degree.  The Lebesgue hypotheses
are pointwise in the displayed nonnode `x`, rather than uniform over all
nonnodes. -/
def claim47250 : Prop :=
  ∀ (n : ℕ) (t : ℕ → ℝ) (B : ℕ → ℝ),
    1 ≤ n →
    prefixNodesDistinct472 t (2 * n) →
    prefixNodesInInterval472 t (2 * n) →
    (∀ m : ℕ, n ≤ m → m < 2 * n →
      ∀ x : ℝ, (∀ i : Fin (m + 1), x ≠ t i.1) →
        |prefixLagrangeFactor472 t (m + 1) (Fin.last m) x| =
          |(prefixPolynomial472 t m).eval x| /
            |(prefixPolynomial472 t m).eval (t m)|) ∧
    (∀ x : ℝ, (∀ i : Fin (2 * n), x ≠ t i.1) →
      ((∀ m : ℕ, n ≤ m → m < 2 * n →
          prefixLebesgue472 t (m + 1) x ≤ B (m + 1)) →
        ∏ m ∈ Finset.Ico n (2 * n),
            |(prefixPolynomial472 t m).eval x| ≤
          (∏ m ∈ Finset.Ico n (2 * n), B (m + 1)) *
            (prefixVandermonde472 t (2 * n) /
              prefixVandermonde472 t n))) ∧
    (productPrefixPolynomial472 t n).Monic ∧
      (productPrefixPolynomial472 t n).natDegree = n * (3 * n - 1) / 2

end MathlibPlus.Open.Algebra.R3343LagrangeRepair
