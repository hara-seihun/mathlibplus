import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

open scoped BigOperators

noncomputable section

/-- The folded arithmetic density on the unit cell with integer index `n`. -/
def foldedArithmeticUnitCellDensity (n : ℤ) (u : ℝ) : ℝ :=
  ∫ x in (n : ℝ)..((n + 1 : ℤ) : ℝ),
    x * (x - (n : ℝ)) *
      (Real.exp (-5 * u / 2 - Real.pi * x ^ 2 * Real.exp (-2 * u)) +
        Real.exp (5 * u / 2 - Real.pi * x ^ 2 * Real.exp (2 * u)))

/-- The even moment of a folded arithmetic unit cell. -/
def foldedArithmeticUnitCellMoment (n : ℤ) (j : ℕ) : ℝ :=
  ∫ u in Set.Ioi (0 : ℝ),
    u ^ (2 * j) * foldedArithmeticUnitCellDensity n u

/-- Factorial transport of a moment sequence to completed jet coefficients. -/
def factorialJetCoefficient (m : ℕ → ℝ) (j : ℕ) : ℝ :=
  m j / (Nat.factorial (2 * j) : ℝ)

/-- The completed checkerboard Bezout matrix from a completed coefficient sequence. -/
def completedCheckerboardBezoutMatrix (h : ℕ → ℝ) (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j =>
    ∑ a ∈ Finset.range (min i.1 j.1 + 1),
      (↑(i.1 + j.1 + 1 - 2 * a) : ℝ) * h a * h (i.1 + j.1 + 1 - a)

/-- The rank-two completed Bezout determinant. -/
def completedBezoutRankTwoDeterminant (h : ℕ → ℝ) : ℝ :=
  Matrix.det (completedCheckerboardBezoutMatrix h 2)

/-- The rank-three completed Bezout determinant. -/
def completedBezoutRankThreeDeterminant (h : ℕ → ℝ) : ℝ :=
  Matrix.det (completedCheckerboardBezoutMatrix h 3)

/-- The integer-normalized rank-two quantity used for moment sequences. -/
def completedBezoutRankTwoQuantity (m : ℕ → ℝ) : ℝ :=
  (1440 : ℝ) * completedBezoutRankTwoDeterminant (fun j => factorialJetCoefficient m j) / m 0

/-- The rank-three integer normalization used in the exact three-atom witness. -/
def completedBezoutRankThreeQuantity (m : ℕ → ℝ) : ℝ :=
  (36578304000 : ℝ) *
    completedBezoutRankThreeDeterminant (fun j => factorialJetCoefficient m j)

/-- The two-cell positive mixture from the certified witness. -/
def twoCellMixedMoment (j : ℕ) : ℝ :=
  foldedArithmeticUnitCellMoment 1 j + (27 / 2 : ℝ) * foldedArithmeticUnitCellMoment 30 j

/-- The ordinary Stieltjes ratio `R`. -/
def ordinaryMomentRatioR (m : ℕ → ℝ) : ℝ :=
  (m 1) ^ 2 / (m 0 * m 2)

/-- The ordinary Stieltjes ratio `S`. -/
def ordinaryMomentRatioS (m : ℕ → ℝ) : ℝ :=
  (m 1 * m 3) / (m 2) ^ 2

/--
Cellwise positivity and the genuine folded arithmetic cell carrier do not force
rank-two completed Bezout positivity, even for the certified two-cell mixture.
-/
def positiveGenuineCellMixturesDoNotForceRankTwoPositivityClaim : Prop :=
  let m : ℕ → ℝ := twoCellMixedMoment
  let h : ℕ → ℝ := fun j => factorialJetCoefficient m j
  (∀ n : ℤ, 0 < n → ∀ u : ℝ, 0 ≤ u → 0 ≤ foldedArithmeticUnitCellDensity n u) ∧
    (0 < (1 : ℝ) ∧ 0 < (27 / 2 : ℝ)) ∧
    (∀ j : ℕ,
      m j =
        (1 : ℝ) * foldedArithmeticUnitCellMoment 1 j +
          (27 / 2 : ℝ) * foldedArithmeticUnitCellMoment 30 j) ∧
    (∀ j : ℕ, h j = m j / (Nat.factorial (2 * j) : ℝ)) ∧
    0 < ordinaryMomentRatioR m ∧ ordinaryMomentRatioR m < 1 ∧
    1 < ordinaryMomentRatioS m ∧
    completedBezoutRankTwoDeterminant h < 0

/-- The exact moment carrier of `A δ₀ + B δ_z`. -/
def twoAtomMoment (A B z : ℝ) (j : ℕ) : ℝ :=
  if j = 0 then A + B else B * z ^ j

/-- The completed rank-two determinant quantity of the two-atom family. -/
def twoAtomRankTwoQuantity (A B z : ℝ) : ℝ :=
  completedBezoutRankTwoQuantity (twoAtomMoment A B z)

/-- The completed rank-three determinant quantity of the two-atom family. -/
def twoAtomRankThreeQuantity (A B z : ℝ) : ℝ :=
  completedBezoutRankThreeQuantity (twoAtomMoment A B z)

/-- The exact closed formula for the two-atom rank-two quantity. -/
def twoAtomRankTwoFormula (A B z : ℝ) : ℝ :=
  -B ^ 2 * z ^ 4 * (7 * A - 8 * B)

/-- The exact closed formula for the two-atom rank-three quantity. -/
def twoAtomRankThreeFormula (A B z : ℝ) : ℝ :=
  -B ^ 3 * z ^ 9 * (A + B) * (551 * A ^ 2 + 472 * A * B - 1024 * B ^ 2)

/-- The sharp rank-two/rank-three wall for the positive two-atom family. -/
def sharpTwoAtomRankWallClaim : Prop :=
  let r₃ : ℝ := (-236 + 12 * Real.sqrt 4305) / 551
  (∀ A B z : ℝ, 0 < A → 0 < B → 0 < z →
    twoAtomRankTwoQuantity A B z = twoAtomRankTwoFormula A B z ∧
      twoAtomRankThreeQuantity A B z = twoAtomRankThreeFormula A B z ∧
      (0 < twoAtomRankTwoQuantity A B z ↔ A / B < 8 / 7) ∧
      (0 < twoAtomRankThreeQuantity A B z ↔ A / B < r₃)) ∧
    1 < r₃ ∧ r₃ < 11 / 10 ∧ 11 / 10 < (8 / 7 : ℝ) ∧
    (∀ A B z : ℝ, 0 < A → 0 < B → 0 < z →
      r₃ < A / B → A / B < 8 / 7 →
        0 < twoAtomRankTwoQuantity A B z ∧ twoAtomRankThreeQuantity A B z < 0) ∧
    (∀ A B z : ℝ, 0 < A → 0 < B → 0 < z → A / B = 11 / 10 →
      0 < twoAtomRankTwoQuantity A B z ∧ twoAtomRankThreeQuantity A B z < 0)

/-- A weighted moment curve with all increasing square minors strict through rank three. -/
def strictWeightedVandermondeThroughRankThree (x w : Fin 3 → ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → k ≤ 3 →
    ∀ rows : Fin k → Fin 3, StrictMono rows →
      ∀ exponents : Fin k → ℕ, StrictMono exponents →
        0 < Matrix.det (fun i j => w (rows i) * (x (rows i)) ^ exponents j)

/-- Strict positive definiteness of a real square matrix. -/
def strictlyPositiveDefinite {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ v : Fin n → ℝ, v ≠ 0 →
    0 < ∑ i, ∑ j, v i * M i j * v j

/-- An ordinary or shifted truncated Hankel moment matrix. -/
def truncatedHankelMatrix (m : ℕ → ℝ) (shift size : ℕ) : Matrix (Fin size) (Fin size) ℝ :=
  fun i j => m (i.1 + j.1 + shift)

/-- Strict ordinary and shifted Stieltjes positivity through rank three. -/
def strictTruncatedStieltjesThroughRankThree (m : ℕ → ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → k ≤ 3 →
    strictlyPositiveDefinite (truncatedHankelMatrix m 0 k) ∧
      strictlyPositiveDefinite (truncatedHankelMatrix m 1 k)

/-- The three-atom moment carrier `10 δ₁ + δ₂ + 2 δ₇`. -/
def threeAtomMoment (j : ℕ) : ℝ :=
  10 * (1 : ℝ) ^ j + (2 : ℝ) ^ j + 2 * (7 : ℝ) ^ j

/-- The normalized variance ratio from a moment sequence. -/
def normalizedVariance (m : ℕ → ℝ) : ℝ :=
  m 0 * m 2 / (m 1) ^ 2

/-- The final shifted Hankel slack used by the three-atom witness. -/
def finalHankelSlack (m : ℕ → ℝ) : ℝ :=
  m 3 * m 5 - (m 4) ^ 2

/--
The strict Stieltjes and weighted-Vandermonde hypotheses, positive rank two,
and the exact variance and final-slack data can coexist with negative rank three.
-/
def normalizedVarianceDoesNotControlStrictInteriorRankThreeClaim : Prop :=
  let m : ℕ → ℝ := threeAtomMoment
  (m 0 = 13 ∧ m 1 = 26 ∧ m 2 = 112 ∧ m 3 = 704 ∧ m 4 = 4828 ∧ m 5 = 33656) ∧
    strictWeightedVandermondeThroughRankThree ![1, 2, 7] ![10, 1, 2] ∧
    strictTruncatedStieltjesThroughRankThree m ∧
    normalizedVariance m = 28 / 13 ∧ 28 / 13 > 15 / 7 ∧
    finalHankelSlack m = 384240 ∧ 0 < finalHankelSlack m ∧
    0 < completedBezoutRankTwoDeterminant (fun j => factorialJetCoefficient m j) ∧
    completedBezoutRankTwoQuantity m = 218816 ∧
    0 < completedBezoutRankTwoQuantity m ∧
    completedBezoutRankThreeQuantity m = -23793618030208 ∧
    completedBezoutRankThreeDeterminant (fun j => factorialJetCoefficient m j) < 0 ∧
    completedBezoutRankThreeQuantity m < 0

/-- Prime logarithmic activity `p^{-z}` in its exponential normalization. -/
def primeLogarithmicActivity (p : ℕ) (z : ℂ) : ℂ :=
  Complex.exp (-z * (Real.log (p : ℝ) : ℂ))

/-- The positive-coefficient reciprocal Laurent defect from the exact witness. -/
def palindromicDefect (q : ℂ) : ℂ :=
  5 + 2 * (q + q⁻¹)

/-- The odd root-height parameter for the activity equations. -/
def oddActivityHeight (k : ℤ) : ℝ :=
  ((2 * k + 1 : ℤ) : ℝ) * Real.pi / Real.log 2

/-- The two vertical zero lines in the `z`-plane. -/
def positiveActivityZeroLine (k : ℤ) : ℂ :=
  (1 : ℂ) - (oddActivityHeight k : ℂ) * Complex.I

def negativeActivityZeroLine (k : ℤ) : ℂ :=
  (-1 : ℂ) - (oddActivityHeight k : ℂ) * Complex.I

/-- The exact off-axis zero lines of the palindromic defect under `q = 2^{-z}`. -/
def exactOffAxisZeroLinesForPalindromicDefectClaim : Prop :=
  (∀ q : ℂ, q ≠ 0 →
    q * palindromicDefect q = 2 * q ^ 2 + 5 * q + 2 ∧
      2 * q ^ 2 + 5 * q + 2 = (2 * q + 1) * (q + 2)) ∧
    (∀ q : ℂ, q ≠ 0 →
      (palindromicDefect q = 0 ↔ q = -(1 / 2 : ℂ) ∨ q = -(2 : ℂ))) ∧
    (∀ q : ℂ, palindromicDefect q = 0 → palindromicDefect q⁻¹ = 0) ∧
    (∀ k : ℤ,
      primeLogarithmicActivity 2 (positiveActivityZeroLine k) = -(1 / 2 : ℂ) ∧
        primeLogarithmicActivity 2 (negativeActivityZeroLine k) = -(2 : ℂ)) ∧
    (∀ z : ℂ,
      palindromicDefect (primeLogarithmicActivity 2 z) = 0 ↔
        ∃ k : ℤ,
          z = positiveActivityZeroLine k ∨ z = negativeActivityZeroLine k) ∧
    (∀ z : ℂ,
      palindromicDefect (primeLogarithmicActivity 2 z) = 0 →
        (z.re = 1 ∨ z.re = -1) ∧ z.re ≠ 0)

end

end MathlibPlus.Open.ResearchFormalization
