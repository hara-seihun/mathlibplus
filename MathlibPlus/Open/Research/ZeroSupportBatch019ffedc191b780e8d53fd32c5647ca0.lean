import Mathlib

open scoped BigOperators
open MeasureTheory

namespace MathlibPlus.Open.Research.ZeroSupportBatch019ffedc

/-- The explicit cubic appearing in the zero-support factor. -/
noncomputable def zeroSupportCubic (z : ℝ) : ℝ :=
  479249 * z ^ 3 - 2029584 * z ^ 2 - 546816 * z + 2097152

/-- The explicit normalized zero-support factor from the admitted packet. -/
noncomputable def zeroSupportFactor (z : ℝ) : ℝ :=
  (1 + z) * zeroSupportCubic z / 2097152

noncomputable def zeroSupportLogFactor (z : ℝ) : ℝ :=
  Real.log (zeroSupportFactor z)

/-- Claim 10693: exact zero geometry and all logarithmic-derivative signs. -/
def claim10693 : Prop :=
  ∃ a b c : ℝ,
    (-1.027 : ℝ) < -a ∧ -a < -1.026 ∧
    (1 : ℝ) < b ∧ b < 1.001 ∧
    4.261 < c ∧ c < 4.262 ∧
    zeroSupportCubic (-a) = 0 ∧
    zeroSupportCubic b = 0 ∧
    zeroSupportCubic c = 0 ∧
    (∀ x : ℝ, zeroSupportCubic x = 0 →
      x = -a ∨ x = b ∨ x = c) ∧
    a > 1 ∧ b > 1 ∧ c > a ∧
    (∀ m : ℕ, 1 ≤ m →
      iteratedDeriv m zeroSupportLogFactor 0 =
        -(Nat.factorial (m - 1) : ℝ) *
          (((-1 : ℝ) ^ m) + ((-a)⁻¹) ^ m + b⁻¹ ^ m + c⁻¹ ^ m)) ∧
    (∀ m : ℕ, 1 ≤ m →
      (Odd m ∧ 0 < iteratedDeriv m zeroSupportLogFactor 0) ∨
      (Even m ∧ iteratedDeriv m zeroSupportLogFactor 0 < 0))

/-- The zero-support integral used by Claims 10700 and 10708. -/
noncomputable def zeroSupportPhi (M : ℕ) (lam : ℝ) : ℝ :=
  ∫ t, Real.exp (-t) *
      (1 - Finset.prod (Finset.Icc 2 M)
        (fun n => 1 - lam * t / Real.sqrt (n : ℝ))) / t
      ∂(volume.restrict (Set.Ioi (0 : ℝ)))

/-- The lower bound named in Claim 10708. -/
noncomputable def zeroSupportLower (M : ℕ) : ℝ :=
  Real.exp (-((M : ℝ) + 1)) *
      (M : ℝ) ^ (M - 1) *
      Real.exp (-3 * Real.sqrt (M : ℝ) / 4) /
      (2 * ((M : ℝ) + 1) * Real.sqrt (Nat.factorial M : ℝ))

/-- The opposite-sign bound named in Claim 10708. -/
noncomputable def zeroSupportUpper (M : ℕ) : ℝ :=
  2 * Real.sqrt (M : ℝ) *
      (3 : ℝ) ^ (M - 1) *
      (M : ℝ) ^ (((M : ℝ) - 1) / 2) /
      Real.sqrt (Nat.factorial M : ℝ)

/-- Claim 10700: every odd zero-support prefix from three onward is negative. -/
def claim10700 : Prop :=
  ∀ M : ℕ, 3 ≤ M → Odd M → zeroSupportPhi M 1 < 0

/-- Claim 10708: the stated factorial bounds and parity signs for large prefixes. -/
def claim10708 : Prop :=
  ∀ M : ℕ, 305 ≤ M →
    ((Even M ∧ 0 < zeroSupportPhi M 1) ∨
      (Odd M ∧ zeroSupportPhi M 1 < 0)) ∧
    |zeroSupportPhi M 1| ≥ zeroSupportLower M - zeroSupportUpper M

end MathlibPlus.Open.Research.ZeroSupportBatch019ffedc
