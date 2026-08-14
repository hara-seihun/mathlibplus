import Mathlib

namespace MathlibPlus.Open.BpsBatch

noncomputable section

abbrev BpsSeries := MvPowerSeries (Fin 2) ℚ

def xAtom : BpsSeries := MvPowerSeries.X (0 : Fin 2)

def yAtom : BpsSeries := MvPowerSeries.X (1 : Fin 2)

def xyIndex : (Fin 2 →₀ ℕ) :=
  Finsupp.single (0 : Fin 2) 1 + Finsupp.single (1 : Fin 2) 1

def integerPower (z : BpsSeries) : ℤ → BpsSeries
  | Int.ofNat n => z ^ n
  | Int.negSucc n => (z⁻¹) ^ (n + 1)

def partitionSeries (Ω : ℤ) : BpsSeries :=
  ((1 - xAtom) * (1 - yAtom) * integerPower (1 - xAtom * yAtom) Ω)⁻¹

/-- The coefficient of `xy` in the formal logarithm.  At this bidegree
only the first two terms of `U - U^2/2 + ...`, with `U = Z - 1`, can
contribute. -/
def xyLogCoefficient (Z : BpsSeries) : ℚ :=
  MvPowerSeries.coeff xyIndex
    ((Z - 1) - (1 / 2 : ℚ) • (Z - 1) ^ 2)

def primePowerIndex (n : ℕ) : Prop :=
  ∃ p m : ℕ, Nat.Prime p ∧ 1 ≤ m ∧ n = p ^ m

def primePowerSupported (c : ℕ → ℚ) : Prop :=
  ∀ n : ℕ, c n ≠ 0 → primePowerIndex n

def mixedAtomLabel (s : ℝ) : ℝ := Real.rpow 6 (-s)

def mixedBpsChargeClaim (Ω : ℤ) : Prop :=
  xyLogCoefficient (partitionSeries Ω) = (Ω : ℚ) ∧
  (Ω ≠ 0 →
    (∀ s : ℝ,
      Real.rpow 2 (-s) * Real.rpow 3 (-s) = mixedAtomLabel s) ∧
    ¬ ∃ c : ℕ → ℚ,
      primePowerSupported c ∧ c 6 = (Ω : ℚ))

end

end MathlibPlus.Open.BpsBatch
