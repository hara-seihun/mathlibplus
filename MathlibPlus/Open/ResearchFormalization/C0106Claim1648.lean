import Mathlib
import MathlibPlus.Open.Algebra.C0106Claim1651
import MathlibPlus.Open.Analysis.ClearedStripPositivity

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.C0106Claim1648

noncomputable section

abbrev BatchPolynomial1648 := MvPolynomial (Fin 2) ℚ

def bVariable1648 : BatchPolynomial1648 := MvPolynomial.X 0

def mVariable1648 : BatchPolynomial1648 := MvPolynomial.X 1

def rationalConstant1648 (q : ℚ) : BatchPolynomial1648 := MvPolynomial.C q

def ratNat1648 (n : ℕ) : ℚ := n

def risingPolynomial1648 (x : BatchPolynomial1648) (k : ℕ) : BatchPolynomial1648 :=
  ∏ i ∈ Finset.range k, (x + rationalConstant1648 (ratNat1648 i))

def risingMPolynomial1648 (x : Polynomial ℚ) (k : ℕ) : Polynomial ℚ :=
  ∏ i ∈ Finset.range k, (x + Polynomial.C (ratNat1648 i))

/-- The two coefficient polynomials appearing in the displayed correction. -/
def A1648 (n : ℕ) : BatchPolynomial1648 :=
  rationalConstant1648 (ratNat1648 (n + 2)) * mVariable1648 ^ 2 +
    rationalConstant1648 (ratNat1648 (2 * n ^ 2 + 2 * n - 1)) * mVariable1648 +
    rationalConstant1648 (ratNat1648 ((n - 1) * (n + 1) ^ 2))

def B1648 (n : ℕ) : BatchPolynomial1648 :=
  rationalConstant1648 (ratNat1648 (n + 1)) * mVariable1648 ^ 2 +
    rationalConstant1648 (ratNat1648 (2 * n ^ 2 - n - 3)) * mVariable1648 +
    rationalConstant1648 (ratNat1648 ((n - 1) * (n - 2) * (n + 1)))

/-- The one-variable factors in `m` that occur in the displayed formula. -/
def APolynomial1648 (n : ℕ) : Polynomial ℚ :=
  Polynomial.C (ratNat1648 (n + 2)) * Polynomial.X ^ 2 +
    Polynomial.C (ratNat1648 (2 * n ^ 2 + 2 * n - 1)) * Polynomial.X +
    Polynomial.C (ratNat1648 ((n - 1) * (n + 1) ^ 2))

def BPolynomial1648 (n : ℕ) : Polynomial ℚ :=
  Polynomial.C (ratNat1648 (n + 1)) * Polynomial.X ^ 2 +
    Polynomial.C (ratNat1648 (2 * n ^ 2 - n - 3)) * Polynomial.X +
    Polynomial.C (ratNat1648 ((n - 1) * (n - 2) * (n + 1)))

def uMPolynomial1648 (n : ℕ) : Polynomial ℚ :=
  (Polynomial.X + Polynomial.C (ratNat1648 (2 * n))) *
    risingMPolynomial1648
      (Polynomial.X + Polynomial.C 1) (n - 1) *
    Polynomial.C (1 / ratNat1648 (Nat.factorial n))

def coefficientwiseNonnegativeM1648 (p : Polynomial ℚ) : Prop :=
  ∀ k : ℕ, 0 ≤ p.coeff k

def factorwiseNonnegative1648 (n : ℕ) : Prop :=
  coefficientwiseNonnegativeM1648 (uMPolynomial1648 n) ∧
    coefficientwiseNonnegativeM1648
      (Polynomial.X + Polynomial.C (ratNat1648 (2 * n))) ∧
    coefficientwiseNonnegativeM1648
      (risingMPolynomial1648 (Polynomial.X + Polynomial.C 1) (n - 2)) ∧
    coefficientwiseNonnegativeM1648 (APolynomial1648 n) ∧
    coefficientwiseNonnegativeM1648
      (Polynomial.X + Polynomial.C (ratNat1648 (n + 1))) ∧
    coefficientwiseNonnegativeM1648 (BPolynomial1648 n)

/-- The source rising-factorial definition of `u_n(m)`. -/
def uPolynomial1648 (n : ℕ) : BatchPolynomial1648 :=
  (mVariable1648 + rationalConstant1648 (ratNat1648 (2 * n))) *
    risingPolynomial1648
      (mVariable1648 + rationalConstant1648 1) (n - 1) *
    rationalConstant1648 (1 / ratNat1648 (Nat.factorial n))

/-- The displayed polynomial in the indeterminates `b,m`. -/
def KPolynomial1648 (n : ℕ) : BatchPolynomial1648 :=
  rationalConstant1648 4 * uPolynomial1648 n * bVariable1648 ^ 2 +
    rationalConstant1648
        (2 / (ratNat1648 (n + 1) * ratNat1648 (Nat.factorial n))) *
      (mVariable1648 + rationalConstant1648 (ratNat1648 (2 * n))) *
      risingPolynomial1648
        (mVariable1648 + rationalConstant1648 1) (n - 2) *
      A1648 n * bVariable1648 +
    rationalConstant1648
        (1 / (2 * ratNat1648 (n + 1) * ratNat1648 (Nat.factorial n))) *
      (mVariable1648 + rationalConstant1648 (ratNat1648 (2 * n))) *
      (mVariable1648 + rationalConstant1648 (ratNat1648 (n + 1))) *
      risingPolynomial1648
          (mVariable1648 + rationalConstant1648 1) (n - 2) *
      B1648 n

/-- Coefficientwise nonnegativity for the two-variable rational polynomial. -/
def coefficientwiseNonnegative1648 (p : BatchPolynomial1648) : Prop :=
  ∀ c : Fin 2 →₀ ℕ, 0 ≤ p.coeff c

/-- Evaluation of a two-variable polynomial at `(b,m)`. -/
def eval1648 (p : BatchPolynomial1648) (b m : ℝ) : ℝ :=
  MvPolynomial.eval₂ (algebraMap ℚ ℝ)
    (fun i : Fin 2 => if i.1 = 0 then b else m) p

/-- The source rising-factorial value `u_n(m)`. -/
def uValue1648 (n m : ℕ) : ℚ :=
  ratNat1648 (m + 2 * n) *
    Finset.prod (Finset.range (n - 1)) (fun i =>
      ratNat1648 (m + 1) + ratNat1648 i) /
    ratNat1648 (Nat.factorial n)

/-- The cleared hook correction from the source recurrence. -/
def sourceHookCorrection1648 (n m : ℕ) (b : ℝ) : ℝ :=
  (uValue1648 n m : ℝ) *
    (2 * b +
      (m : ℝ) * ((m : ℝ) - 1) /
        (((n : ℝ) + 1) * ((m : ℝ) + (n : ℝ) - 1)))

/-- The source definition `K_n=(2b+m+n+1)C_n+W_n(m+n)`, with the
closed neighboring-minor amplitude `W_n` retained as its concrete product. -/
def sourceK1648 (n m : ℕ) (b : ℝ) : ℝ :=
  (2 * b + (m : ℝ) + (n : ℝ) + 1) *
      sourceHookCorrection1648 n m b +
    (MathlibPlus.Open.Algebra.C0106Claim1651.W1651 n (m + n) : ℝ)

/-- Claim 1648: the source correction is the displayed polynomial, and its
rational coefficients are all nonnegative for `n≥2`. -/
def claim1648 : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    (∀ (m : ℕ) (b : ℝ),
      sourceK1648 n m b = eval1648 (KPolynomial1648 n) b m) ∧
    factorwiseNonnegative1648 n ∧
    coefficientwiseNonnegative1648 (KPolynomial1648 n)

end

end MathlibPlus.Open.ResearchFormalization.C0106Claim1648
