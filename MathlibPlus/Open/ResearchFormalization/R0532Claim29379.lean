import MathlibPlus.Open.ResearchFormalization.BatchR0532Claims29380_29381

namespace MathlibPlus.Open.ResearchFormalization.R0532Claim29379

open MathlibPlus.Open.ResearchFormalization.BatchR0532

noncomputable section

/-- The first leg length at which two oriented large-side multisets differ,
with its signed multiplicity difference. -/
def firstDifference29379
    (large large' : Multiset ℕ) (k : ℕ) : Prop :=
  (∀ j : ℕ, j < k → large.count j = large'.count j) ∧
    (large.count k : ℤ) - (large'.count k : ℤ) ≠ 0

/-- Claim 29379: in the exact admissible adjacent 2-by-r grouping carrier,
the first differing leg coefficient of the exceptional z^(r+2) functional is
2 times the signed multiplicity difference and is nonzero. -/
def claim29379 : Prop :=
  ∀ (U : Multiset ℕ) (N r : ℕ)
    (large small large' small' : Multiset ℕ),
    admissibleTwoByRGrouping U N r large small →
      admissibleTwoByRGrouping U N r large' small' →
        large ≠ large' →
          ∃ k : ℕ,
          firstDifference29379 large large' k ∧
            (exceptionalGroupingFunctional N large small -
                exceptionalGroupingFunctional N large' small').coeff k =
              2 * ((large.count k : ℤ) - (large'.count k : ℤ)) ∧
            (exceptionalGroupingFunctional N large small -
                exceptionalGroupingFunctional N large' small').coeff k ≠ 0

end

end MathlibPlus.Open.ResearchFormalization.R0532Claim29379
