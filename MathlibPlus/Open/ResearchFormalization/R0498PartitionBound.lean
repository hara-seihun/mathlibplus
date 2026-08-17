import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0498PartitionBound

noncomputable section

/-- The explicit positive-part formula for the ceiling `U`; the aligned
statement below uses it on the source domain `1 ≤ ell`. -/
def ceilingU (ell N : ℕ) : ℕ :=
  1 +
      ∑ a ∈ Finset.Icc 1 (((ell + 1) / 2) - 1),
        (N + 1 - 2 * a) +
    if Even ell then ((N + 2) / 2 - ell / 2) else 0

/-- The finite count of partitions of `N` having at most `ell` parts. -/
def partitionCount (ell N : ℕ) : ℕ :=
  (Finset.univ.filter
    (fun p : Nat.Partition N => p.parts.card ≤ ell)).card

/-- Claim 29359: the ceiling is the active minimum in every positive-`ell`
cell. -/
def ceilingNeverExceedsPartitionCount : Prop :=
  ∀ ell N : ℕ, 1 ≤ ell →
    ceilingU ell N ≤ partitionCount ell N ∧
      min (partitionCount ell N) (ceilingU ell N) = ceilingU ell N

end
end MathlibPlus.Open.ResearchFormalization.R0498PartitionBound
