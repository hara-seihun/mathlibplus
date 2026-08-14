import Mathlib

namespace MathlibPlus.Open.Research

noncomputable section

open scoped BigOperators

/-- The constant used by the central Charlier recurrence. -/
def centralCharlierA : ℝ := 5 / 4

/-- The signed sheet coordinate from the mixed-row determinant model. -/
def sheetCoordinate (q L ε : ℝ) : ℝ :=
  ε * (5 / 4 - q * Real.rpow L ε)

/-- The three-coordinate row `R(q, ε)` in the mixed-row model. -/
def sheetRow (q L ε : ℝ) : Fin 3 → ℝ := fun j =>
  match j.1 with
  | 0 => 1
  | 1 => sheetCoordinate q L ε
  | _ => sheetCoordinate q L ε ^ 2 + ε * sheetCoordinate q L ε - 5 / 4

/-- The determinant of three rows of length three. -/
def detThree (r₁ r₂ r₃ : Fin 3 → ℝ) : ℝ :=
  r₁ 0 * (r₂ 1 * r₃ 2 - r₂ 2 * r₃ 1)
    - r₁ 1 * (r₂ 0 * r₃ 2 - r₂ 2 * r₃ 0)
    + r₁ 2 * (r₂ 0 * r₃ 1 - r₂ 1 * r₃ 0)

/-- The physical weights in the mixed-row determinant model. -/
def physicalWeight (A L : ℝ) : ℝ :=
  Real.rpow L (5 / 2 : ℝ) * Real.exp (-2 * A * Real.sinh (Real.log L))

/-- A mixed row `R(q,-1) + w R(q,+1)`. -/
def mixedSheetRow (q L w : ℝ) : Fin 3 → ℝ :=
  sheetRow q L (-1) + w • sheetRow q L 1

/-- The determinant `B` of the mixed-row model. -/
def mixedRowDeterminant (q₁ A d L : ℝ) : ℝ :=
  detThree
    (sheetRow q₁ L 1)
    (mixedSheetRow A L (physicalWeight A L))
    (mixedSheetRow (A + d) L (physicalWeight (A + d) L))

/-- The exact separated-chamber positivity assertion for the mixed-row determinant. -/
def separatedChamberMixedRowPositivity : Prop :=
  ∀ q₁ A d L : ℝ,
    3 ≤ q₁ →
    12 ≤ A →
    0 < d →
    27 ≤ A + d →
    1 ≤ L →
    0 < mixedRowDeterminant q₁ A d L

/-- The central Charlier polynomials. -/
def centralCharlier : ℕ → Polynomial ℝ
  | 0 => 1
  | m + 1 =>
      Polynomial.X * Polynomial.derivative (centralCharlier m)
        + (Polynomial.C centralCharlierA - Polynomial.X) * centralCharlier m

/-- The exact exponential generating-function identity for the central Charlier polynomials. -/
def centralCharlierGeneratingFunction : Prop :=
  ∀ q s : ℝ,
    HasSum
      (fun m : ℕ =>
        Polynomial.eval q (centralCharlier m) * s ^ m / (m.factorial : ℝ))
      (Real.exp (centralCharlierA * s + q * (1 - Real.exp s)))

/-- The wall parameter `q_n = π n²`. -/
def wallParameter (n : ℕ) : ℝ := Real.pi * (n : ℝ) ^ 2

/-- The reflected two-sheet wall kernel. -/
def wallKernel (n : ℕ) (t : ℝ) : ℝ :=
  Real.exp (-centralCharlierA * t - wallParameter n * Real.exp (-t))
    + Real.exp (centralCharlierA * t + -wallParameter n * Real.exp t)

/-- The even Taylor-series summand in the integer-wall expansion. -/
def wallEvenTerm (n j : ℕ) (t : ℝ) : ℝ :=
  2 * Real.exp (-wallParameter n)
    * (Polynomial.eval (wallParameter n) (centralCharlier (2 * j))
      * t ^ (2 * j) / ((2 * j).factorial : ℝ))

/-- Pointwise convergence and equality of the locally convergent even expansion. -/
def wallEvenExpansion : Prop :=
  ∀ n : ℕ, ∀ t : ℝ,
    HasSum (fun j : ℕ => wallEvenTerm n j t) (wallKernel n t)

/-- The wall-kernel matrix for a finite ordered selection of rows and columns. -/
def wallMatrix (r : ℕ) (n : Fin r → ℕ) (t : Fin r → ℝ) :
    Matrix (Fin r) (Fin r) ℝ :=
  fun i j => wallKernel (n i) (t j)

/-- The arithmetic coefficient minor in the all-rank expansion. -/
def charlierMinor (r : ℕ) (n k : Fin r → ℕ) : ℝ :=
  Matrix.det (fun i j =>
    Polynomial.eval (wallParameter (n i)) (centralCharlier (2 * k j)))

/-- The generalized monomial alternant in the all-rank expansion. -/
def monomialAlternant (r : ℕ) (t : Fin r → ℝ) (k : Fin r → ℕ) : ℝ :=
  Matrix.det (fun i j =>
    t i ^ (2 * k j) / ((2 * k j).factorial : ℝ))

/-- The all-rank Cauchy--Binet expansion and positivity of its monomial factors. -/
def wallCauchyBinetExpansion : Prop :=
  ∀ (r : ℕ) (n : Fin r → ℕ) (t : Fin r → ℝ),
    StrictMono n →
    (∀ i, 0 < t i) →
    StrictMono t →
    (Matrix.det (wallMatrix r n t) =
      (2 : ℝ) ^ r * Real.exp (-(∑ i, wallParameter (n i))) *
        ∑' k : Fin r → ℕ,
          if StrictMono k then
            charlierMinor r n k * monomialAlternant r t k
          else 0) ∧
    ∀ k : Fin r → ℕ, StrictMono k → 0 < monomialAlternant r t k

/-- A two-by-two arithmetic coefficient minor with two polynomial orders. -/
def twoByTwoCharlierMinor
    (q₁ q₂ : ℝ) (m₁ m₂ : ℕ) : ℝ :=
  Polynomial.eval q₁ (centralCharlier m₁)
      * Polynomial.eval q₂ (centralCharlier m₂)
    - Polynomial.eval q₁ (centralCharlier m₂)
      * Polynomial.eval q₂ (centralCharlier m₁)

/-- The exact negative coefficient minor at orders 26 and 34. -/
def negativeCharlierCoefficientMinor : Prop :=
  twoByTwoCharlierMinor Real.pi (4 * Real.pi) 26 34 < 0

/-- Iterated polynomial differentiation. -/
def iteratedPolynomialDerivative : ℕ → Polynomial ℝ → Polynomial ℝ
  | 0, p => p
  | i + 1, p => Polynomial.derivative (iteratedPolynomialDerivative i p)

/-- The order-14 even central-Charlier wall determinant. -/
def centralCharlierC14 (q : ℝ) : ℝ :=
  Matrix.det (fun i j : Fin 14 =>
    Polynomial.eval q
      (iteratedPolynomialDerivative (i : ℕ) (centralCharlier (2 * (j : ℕ)))))

/-- The exact physical-wall Wronskian sign obstruction. -/
def physicalWallWronskianNegative : Prop :=
  centralCharlierC14 (4 * Real.pi) < 0

/-- The separated even-jet witness coordinates. -/
def separatedWitnessX₁ : ℝ := 2.4525816691261647

def separatedWitnessX₂ : ℝ := 8.8699989668432376

/-- The exact negative nonconsecutive even-jet minor at the separated witness. -/
def separatedEvenJetMinorNegative : Prop :=
  2 < separatedWitnessX₁ ∧ separatedWitnessX₁ < 3 ∧
  8 < separatedWitnessX₂ ∧ separatedWitnessX₂ < 9 ∧
  twoByTwoCharlierMinor
      (Real.pi * separatedWitnessX₁ ^ 2)
      (Real.pi * separatedWitnessX₂ ^ 2)
      12 16 < 0

end

end MathlibPlus.Open.Research
