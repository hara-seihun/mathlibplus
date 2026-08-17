import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R0498FixedEll

noncomputable section

/-- The explicit positive-part formula for the ceiling `U`; the aligned
statement below uses it only on the source domain `1 ≤ ell`. -/
def ceilingU (ell N : ℕ) : ℕ :=
  1 +
      ∑ a ∈ Finset.Icc 1 (((ell + 1) / 2) - 1),
        (N + 1 - 2 * a) +
    if Even ell then ((N + 2) / 2 - ell / 2) else 0

def ceilingSeries (ell : ℕ) : PowerSeries ℚ :=
  PowerSeries.mk (fun N => (ceilingU ell N : ℚ))

def oneMinusXInverse : PowerSeries ℚ :=
  (1 - (PowerSeries.X : PowerSeries ℚ))⁻¹

/-- Claim 29357: the odd and positive-even fixed-`ell` generating functions. -/
def fixedEllCeilingGeneratingFunctions : Prop :=
  (∀ h : ℕ,
    ceilingSeries (2 * h + 1) =
      oneMinusXInverse +
        ∑ a ∈ Finset.range h,
          (PowerSeries.X : PowerSeries ℚ) ^ (2 * (a + 1)) *
            oneMinusXInverse ^ 2) ∧
  (∀ h : ℕ, 1 ≤ h →
    ceilingSeries (2 * h) =
      oneMinusXInverse +
        ∑ a ∈ Finset.range (h - 1),
          (PowerSeries.X : PowerSeries ℚ) ^ (2 * (a + 1)) *
            oneMinusXInverse ^ 2 +
        (PowerSeries.X : PowerSeries ℚ) ^ (2 * h) *
          oneMinusXInverse ^ 2 *
            (1 + (PowerSeries.X : PowerSeries ℚ))⁻¹)

end
end MathlibPlus.Open.ResearchFormalization.R0498FixedEll
