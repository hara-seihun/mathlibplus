import Mathlib
import MathlibPlus.Open.Algebra.NewResearch2.C0112Repair

open scoped BigOperators

namespace MathlibPlus.Open.Algebra.NewResearch2.C0112Repair

noncomputable section

/-- The half-shift multiplier in the arm direction. -/
def armMultiplier (d n : ℕ) : Polynomial ℚ :=
  halfShiftY d + Polynomial.C (((n : ℤ) - 1 : ℤ) : ℚ)

/-- The half-shift multiplier in the strip direction. -/
def stripMultiplier (d k : ℕ) : Polynomial ℚ :=
  halfShiftY d + Polynomial.C (((k : ℤ) - 2 : ℤ) : ℚ)

/-- The arm gap of the cleared correction family. -/
def correctionArmGapE (d n k : ℕ) : Polynomial ℚ :=
  armMultiplier d n * correctionPolynomial d (n - 1) k -
    correctionPolynomial d n k

/-- The arm gap of the numerator family. -/
def correctionArmGapG (d n k : ℕ) : Polynomial ℚ :=
  armMultiplier d n * correctionNumerator d (n - 1) k -
    correctionNumerator d n k

/-- The strip gap of the numerator family. -/
def correctionStripGapL (d n k : ℕ) : Polynomial ℚ :=
  stripMultiplier d k * correctionNumerator d n (k - 1) -
    correctionNumerator d n k

/-- The paired arm remainder. -/
def correctionPairedArmRemainder (d n k : ℕ) : Polynomial ℚ :=
  stripMultiplier d k * correctionArmGapG d n (k - 1) -
    correctionArmGapG d n k

/-- Claim 1754: the uniform correction arm-gap recurrence, its odd-step
paired remainder, and coefficientwise nonnegativity on the full two-row domain. -/
def uniformCorrectionArmGap_claim1754 : Prop :=
  ∀ (d n k : ℕ),
    n ≥ k + 1 → max n (k + 1) ≤ d →
    coefficientwiseNonnegative (correctionArmGapE d n k) ∧
      (1 ≤ k →
        correctionArmGapE d n k =
          stripMultiplier d k * correctionArmGapE d n (k - 1) +
            (-1 : Polynomial ℚ) ^ k * correctionArmGapG d n k ∧
        (Odd k →
          correctionPairedArmRemainder d n k =
              armMultiplier d n * correctionStripGapL d (n - 1) k -
                correctionStripGapL d n k ∧
            coefficientwiseNonnegative (correctionPairedArmRemainder d n k) ∧
            0 < (correctionPairedArmRemainder d n k).coeff 2))

end

end MathlibPlus.Open.Algebra.NewResearch2.C0112Repair
