import Mathlib

namespace MathlibPlus.Open.Ingest.R3186

open scoped Real MeasureTheory
open MeasureTheory

noncomputable section

/-- The exact zero-support rank-four polynomial from admitted claim 48553. -/
def zeroSupportF (z : ℝ) : ℝ :=
  ((1 + z) * (479249 * z ^ 3 - 2029584 * z ^ 2 - 546816 * z + 2097152)) /
    2097152

/-- The cubic factor occurring in `zeroSupportF`. -/
def zeroSupportCubic (z : ℝ) : ℝ :=
  479249 * z ^ 3 - 2029584 * z ^ 2 - 546816 * z + 2097152

/--
The rank-four zero-support factorization, its three real cubic roots with the
reported isolating intervals, and the all-order alternating logarithmic
 derivative sign.
-/
def ZeroSupportAlternatingClaim : Prop :=
  ∃ ρ₁ ρ₂ ρ₃ : ℝ,
    (∀ z : ℝ,
      zeroSupportF z = ((1 + z) * zeroSupportCubic z) / 2097152) ∧
    zeroSupportF (-1) = 0 ∧
    zeroSupportCubic ρ₁ = 0 ∧
    zeroSupportCubic ρ₂ = 0 ∧
    zeroSupportCubic ρ₃ = 0 ∧
    (-1.027 : ℝ) < ρ₁ ∧ ρ₁ < (-1.026 : ℝ) ∧
    (1 : ℝ) < ρ₂ ∧ ρ₂ < (1.001 : ℝ) ∧
    (4.261 : ℝ) < ρ₃ ∧ ρ₃ < (4.262 : ℝ) ∧
    (∀ ρ : ℝ,
      zeroSupportCubic ρ = 0 ↔
        ρ = ρ₁ ∨ ρ = ρ₂ ∨ ρ = ρ₃) ∧
    ∀ m : ℕ, 1 ≤ m →
      0 < ((-1 : ℝ) ^ (m - 1)) *
        iteratedDeriv m (fun t => Real.log (zeroSupportF t)) 0


/-- The displayed positive-scalar log-additive reserve. -/
def positiveScalarReserve (F : ℝ → ℝ) (ν : Measure ℝ) (t : ℝ) : ℝ :=
  ∫ a, Real.log (F (a * t)) ∂ν

/--
The positive-scalar consequence, with the base alternating-sign hypothesis and
explicit integrability needed for the displayed measure integrals.  The
all-order derivative identity is retained as a conclusion rather than hidden
inside an unconstrained analytic interface.
-/
def PositiveScalarReserveClaim (F : ℝ → ℝ) (ν : Measure ℝ) : Prop :=
  0 < ν (Set.Ioi 0) ∧
  ν (Set.Iic 0) = 0 ∧
  (∀ k : ℕ, Integrable (fun a : ℝ => a ^ k) ν) ∧
  (∀ m : ℕ, 1 ≤ m →
    0 < ((-1 : ℝ) ^ (m - 1)) *
      iteratedDeriv m (fun t => Real.log (F t)) 0) ∧
  (∀ t : ℝ, Integrable (fun a : ℝ => Real.log (F (a * t))) ν) ∧
  (∀ m : ℕ, 1 ≤ m →
    Integrable
      (fun a : ℝ => iteratedDeriv m (fun t => Real.log (F (a * t))) 0) ν) ∧
  (∀ m : ℕ, 1 ≤ m →
    0 < ∫ a, a ^ m ∂ν) ∧
  (∀ m : ℕ, 1 ≤ m →
    iteratedDeriv m (positiveScalarReserve F ν) 0 =
      iteratedDeriv m (fun t => Real.log (F t)) 0 *
        (∫ a, a ^ m ∂ν)) ∧
  (∀ m : ℕ, 1 ≤ m →
    0 < ((-1 : ℝ) ^ (m - 1)) *
      iteratedDeriv m (positiveScalarReserve F ν) 0)

end
end MathlibPlus.Open.Ingest.R3186
