import MathlibPlus.Open.Analysis.PrimeScoreBatch

namespace MathlibPlus.Open.Analysis

noncomputable section

/-- Dusart's four-term majorant in the logarithmic variable. -/
def dusartMajorant1214 (x : ℝ) : ℝ :=
  x / Real.log x *
    (1 + 1 / Real.log x + 2 / (Real.log x) ^ 2 +
      (759 : ℝ) / 100 / (Real.log x) ^ 3)

/-- The exact polynomial in the coefficient and logarithmic variable. -/
def dusartQ1214 (c L : ℝ) : ℝ :=
  (c - 1) * L ^ 3 +
    (c + 2 - (759 : ℝ) / 100) * L ^ 2 +
    (2 * c + (759 : ℝ) / 100) * L +
    (759 : ℝ) / 100 * c

/-- The displayed first three derivatives of the cubic. -/
def dusartQPrime1214 (c L : ℝ) : ℝ :=
  3 * (c - 1) * L ^ 2 +
    2 * (c + 2 - (759 : ℝ) / 100) * L +
    (2 * c + (759 : ℝ) / 100)

def dusartQSecond1214 (c L : ℝ) : ℝ :=
  6 * (c - 1) * L + 2 * (c + 2 - (759 : ℝ) / 100)

def dusartQThird1214 (c : ℝ) : ℝ := 6 * (c - 1)

/--
Claim 1214: the exact Dusart-to-`Q_c` comparison and its positive tail at
coefficient 1.149, including the resulting prime-counting target on
`x > 10^19`.
-/
def dusartTailPolynomialComparison_claim1214 : Prop :=
  let c : ℝ := (1149 : ℝ) / 1000
  let L₀ : ℝ := Real.log ((10 : ℝ) ^ (19 : ℕ))
  (∀ x : ℝ, (10 : ℝ) ^ (19 : ℕ) < x →
    let L := Real.log x
    0 < L ∧
      0 < D c x ∧
      (primeCountingReal x : ℝ) ≤ dusartMajorant1214 x ∧
      ((1 / L) *
          (1 + 1 / L + 2 / L ^ 2 + (759 : ℝ) / 100 / L ^ 3) <
        1 / D c x ↔
        0 < dusartQ1214 c L) ∧
      (primeCountingReal x : ℝ) < x / D c x) ∧
    0 < dusartQ1214 c L₀ ∧
    0 < dusartQPrime1214 c L₀ ∧
    0 < dusartQSecond1214 c L₀ ∧
    dusartQThird1214 c = (447 : ℝ) / 500 ∧
    0 < dusartQThird1214 c ∧
    (∀ L : ℝ, L₀ ≤ L → 0 < dusartQ1214 c L)

end

end MathlibPlus.Open.Analysis
