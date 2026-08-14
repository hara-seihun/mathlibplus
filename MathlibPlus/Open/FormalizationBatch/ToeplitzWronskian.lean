import Mathlib

namespace MathlibPlus.Open.FormalizationBatch

noncomputable section

open scoped BigOperators

/-- The factorial-scaled centered Toeplitz matrix attached to a coefficient sequence. -/
def factorialScaledToeplitzMatrix (b : ℕ → ℝ) (r shift : ℕ) :
    Matrix (Fin r) (Fin r) ℝ :=
  fun i j =>
    (Nat.factorial (shift + (j : ℕ) - (i : ℕ)) : ℝ) *
      b (shift + (j : ℕ) - (i : ℕ))

def centeredFactorialToeplitzMinor (b : ℕ → ℝ) (r : ℕ) : ℝ :=
  Matrix.det (factorialScaledToeplitzMatrix b r (r - 1))

def noNegativeCoefficientSubscripts (r shift : ℕ) : Prop :=
  ∀ i j : Fin r, (i : ℕ) ≤ shift + (j : ℕ)

/-- Claim 14821: the factorial-scaled centered minor and its first interior shift. -/
def claim14821 : Prop :=
  noNegativeCoefficientSubscripts 4 3 ∧
    ∀ shift : ℕ, shift < 3 → ¬ noNegativeCoefficientSubscripts 4 shift

def centeredCoefficientPolynomial : Polynomial ℤ :=
  Polynomial.X ^ 2 * (Polynomial.X + 1) ^ 11

def centeredCoefficientPolynomialReal : Polynomial ℝ :=
  Polynomial.X ^ 2 * (Polynomial.X + 1) ^ 11

def derivativeIterate (n : ℕ) (f : Polynomial ℤ) : Polynomial ℤ :=
  Nat.rec f (fun _ g => Polynomial.derivative g) n

def realDerivativeIterate (n : ℕ) (f : Polynomial ℝ) : Polynomial ℝ :=
  Nat.rec f (fun _ g => Polynomial.derivative g) n

def consecutiveDerivativeWronskian (f : Polynomial ℤ) (r : ℕ) : ℤ :=
  Matrix.det (fun i j : Fin r =>
    Polynomial.eval 0 (derivativeIterate (i : ℕ) (derivativeIterate (j : ℕ) f)))

/-- Claim 14822. -/
def claim14822 : Prop :=
  consecutiveDerivativeWronskian centeredCoefficientPolynomial 4 = -1584

def realConsecutiveDerivativeWronskian (f : Polynomial ℝ) (r : ℕ) : ℝ :=
  Matrix.det (fun i j : Fin r =>
    Polynomial.eval 0 (realDerivativeIterate (i : ℕ) (realDerivativeIterate (j : ℕ) f)))

def reciprocalZeroPolynomial {n : ℕ} (x : Fin n → ℝ) : Polynomial ℝ :=
  ∏ i, (1 + (x i) • Polynomial.X)

def negativeRealRoots (p : Polynomial ℝ) : Prop :=
  ∀ z : ℂ,
    Polynomial.IsRoot (p.map Complex.ofRealHom) z →
      z.im = 0 ∧ z.re < 0

def nonpositiveRealRoots (p : Polynomial ℝ) : Prop :=
  ∀ z : ℂ,
    Polynomial.IsRoot (p.map Complex.ofRealHom) z →
      z.im = 0 ∧ z.re ≤ 0

def coefficientSequencePFInfinity (a : ℕ → ℝ) : Prop :=
  ∀ r : ℕ, ∀ row col : Fin r → ℕ,
    StrictMono row → StrictMono col →
      0 ≤ Matrix.det (fun i j : Fin r =>
        if row i ≤ col j then a (col j - row i) else 0)

def bA (A : ℝ) : Polynomial ℝ :=
  (1 + A • Polynomial.X) ^ 2 * (1 + Polynomial.X) ^ 11

/-- Claim 14825. -/
def claim14825 : Prop :=
  ∀ A : ℝ, 0 < A →
    (∀ k : ℕ, 0 ≤ (bA A).coeff k) ∧
    negativeRealRoots (bA A) ∧
    coefficientSequencePFInfinity (fun k => (bA A).coeff k)

def repeatedReciprocalZeros : Fin 13 → ℝ :=
  fun i => if (i : ℕ) < 2 then 162 else 1

def orderFourCenteredMinorOfReciprocalZeros (x : Fin 13 → ℝ) : ℝ :=
  centeredFactorialToeplitzMinor
    (fun k => (reciprocalZeroPolynomial x).coeff k) 4

def claim14835 : Prop :=
  Continuous orderFourCenteredMinorOfReciprocalZeros ∧
    ∃ U : Set (Fin 13 → ℝ),
      IsOpen U ∧ repeatedReciprocalZeros ∈ U ∧
      (∀ x ∈ U, orderFourCenteredMinorOfReciprocalZeros x < 0) ∧
      ∃ x ∈ U,
        (∀ i : Fin 13, 0 < x i) ∧
        (∀ i j : Fin 13, i ≠ j → x i ≠ x j) ∧
        negativeRealRoots (reciprocalZeroPolynomial x)

def factorialCoefficient (p : Polynomial ℝ) (k : ℕ) : ℝ :=
  (Nat.factorial k : ℝ) * p.coeff k

def originWronskianMatrix (p : Polynomial ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => factorialCoefficient p ((i : ℕ) + (j : ℕ))

def reversedCenteredOrderFourMatrix (p : Polynomial ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j =>
    factorialCoefficient p (3 + (j : ℕ) - (i : ℕ))

/-- Claim 14836: row reversal identifies the order-four Wronskian and centered minor. -/
def claim14836 : Prop :=
  ∀ p : Polynomial ℝ,
    Matrix.det (originWronskianMatrix p) =
      Matrix.det (reversedCenteredOrderFourMatrix p)

def orderCenteredMinorOfReciprocalZeros (r : ℕ) {n : ℕ}
    (x : Fin n → ℝ) : ℝ :=
  centeredFactorialToeplitzMinor
    (fun k => (reciprocalZeroPolynomial x).coeff k) r

/-- Claim 14838: the order-four Wronskian counterexample defeats the all-order sign claim. -/
def claim14838 : Prop :=
  (¬ ∀ p : Polynomial ℝ,
      (negativeRealRoots p ∨
        coefficientSequencePFInfinity (fun k => p.coeff k)) →
          ∀ r : ℕ, 0 ≤ realConsecutiveDerivativeWronskian p r) ∧
    nonpositiveRealRoots centeredCoefficientPolynomialReal ∧
    coefficientSequencePFInfinity (fun k => centeredCoefficientPolynomialReal.coeff k) ∧
    realConsecutiveDerivativeWronskian centeredCoefficientPolynomialReal 4 < 0 ∧
    ∃ x : Fin 13 → ℝ,
      (∀ i : Fin 13, 0 < x i) ∧
        (∀ i j : Fin 13, i ≠ j → x i ≠ x j) ∧
        negativeRealRoots (reciprocalZeroPolynomial x) ∧
        realConsecutiveDerivativeWronskian (reciprocalZeroPolynomial x) 4 < 0

/-- Claim 14839: a strict negative centered order-five example exists. -/
def claim14839 : Prop :=
  ∃ n : ℕ, ∃ x : Fin n → ℝ,
    (∀ i : Fin n, 0 ≤ x i) ∧
      orderCenteredMinorOfReciprocalZeros 5 x < 0

end

end MathlibPlus.Open.FormalizationBatch
