import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0498

open scoped BigOperators
noncomputable section

/-- The positive-part ceiling formula used by the admitted cubic statement.
All claims below invoke it only at positive factor number. -/
def cubicCeilingU (ell N : ℕ) : ℕ :=
  1 +
      ∑ a ∈ Finset.Icc 1 (((ell + 1) / 2) - 1),
        (N + 1 - 2 * a) +
    if Even ell then ((N + 2) / 2 - ell / 2) else 0

/-- The exact partition carrier: partitions of `N` having at most `ell` parts. -/
def cubicPartitionCount (ell N : ℕ) : ℕ :=
  (Finset.univ.filter (fun p : Nat.Partition N => p.parts.card ≤ ell)).card

def cubicAntidiagonalCeilingSum (k : ℕ) : ℕ :=
  ∑ ell ∈ Finset.Icc 1 k, cubicCeilingU ell (k - ell)

def cubicAntidiagonalMinimumSum (k : ℕ) : ℕ :=
  ∑ ell ∈ Finset.Icc 1 k,
    min (cubicPartitionCount ell (k - ell))
      (cubicCeilingU ell (k - ell))

def cubicAntidiagonalSeries : PowerSeries ℚ :=
  PowerSeries.mk (fun k => (cubicAntidiagonalCeilingSum k : ℚ))

/-- Claim 29361: both positive-factor antidiagonal identities and the exact
formal-power-series generating function. -/
def cubicAntidiagonalCeilingIdentity : Prop :=
  (∀ k : ℕ, 1 ≤ k →
    cubicAntidiagonalCeilingSum k =
      k + ∑ i ∈ Finset.Icc 2 k, Nat.choose (i / 2) 2) ∧
  (∀ k : ℕ, 1 ≤ k →
    cubicAntidiagonalMinimumSum k =
      k + ∑ i ∈ Finset.Icc 2 k, Nat.choose (i / 2) 2) ∧
  cubicAntidiagonalSeries =
    (PowerSeries.X : PowerSeries ℚ) * (1 - PowerSeries.X)⁻¹ ^ 2 +
      PowerSeries.X ^ 4 * (1 - PowerSeries.X)⁻¹ ^ 4 *
        (1 + PowerSeries.X)⁻¹ ^ 2

end

end MathlibPlus.Open.ResearchFormalization.R0498
