import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R3363Claim46875

/-- Claim 46875: the rational branch child-gap multiset has the displayed
absolute-value form and simplifies at positive branch levels and at level zero
under its stronger sign condition. -/
def branchChildGaps_claim46875 : Prop :=
  (∀ (q s : ℚ) (N : ℕ),
    0 ≤ q →
    |s| ≤ q →
    1 ≤ N →
    ({q * ((N : ℚ) + 3) - |2 * s + q * ((N : ℚ) + 1)|,
      q * ((N : ℚ) + 3) - |2 * s - q * ((N : ℚ) + 1)|} : Multiset ℚ) =
      {2 * (q - s), 2 * (q + s)}) ∧
  (∀ (q s : ℚ),
    2 * |s| ≤ q →
    ({q * 3 - |2 * s + q|,
      q * 3 - |2 * s - q|} : Multiset ℚ) =
      {2 * (q - s), 2 * (q + s)})

end MathlibPlus.Open.ResearchFormalization.R3363Claim46875
