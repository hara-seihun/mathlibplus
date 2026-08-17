import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0498Recurrence

noncomputable section

/-- The explicit positive-part formula for the ceiling `U`; the aligned
statement below uses it on the source domain `1 ≤ ell`. -/
def ceilingU (ell N : ℕ) : ℕ :=
  1 +
      ∑ a ∈ Finset.Icc 1 (((ell + 1) / 2) - 1),
        (N + 1 - 2 * a) +
    if Even ell then ((N + 2) / 2 - ell / 2) else 0

def ceilingSeries (ell : ℕ) : PowerSeries ℚ :=
  PowerSeries.mk (fun N => (ceilingU ell N : ℚ))

def coefficientwiseLE (F G : PowerSeries ℚ) : Prop :=
  ∀ N : ℕ, PowerSeries.coeff N F ≤ PowerSeries.coeff N G

/-- Claim 29358: coefficientwise multiplication by `1 - z^ell` is bounded by
`𝒰_(ell-1)` for every `ell ≥ 2`. -/
def coefficientwiseCeilingRecurrence : Prop :=
  ∀ ell : ℕ, 2 ≤ ell →
    coefficientwiseLE
      ((1 - (PowerSeries.X : PowerSeries ℚ) ^ ell) * ceilingSeries ell)
      (ceilingSeries (ell - 1))

end
end MathlibPlus.Open.ResearchFormalization.R0498Recurrence
