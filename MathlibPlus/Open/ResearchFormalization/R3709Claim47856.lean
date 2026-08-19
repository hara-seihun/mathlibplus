import MathlibPlus.Analysis.Claim49014

namespace MathlibPlus.Open.ResearchFormalization.R3709Claim47856

open scoped BigOperators

noncomputable section

/-- Claim 47856: on the reviewed equal shared-selector area interface, the
    exact all-positive-integer policy area has the displayed closed form and
    is at most two. -/
def sharedSelectorFormulaBound_claim47856 : Prop :=
  ∀ (area preSelector : ℕ → ℚ),
    MathlibPlus.Analysis.Claim49014.sharedSelectorExactArea area preSelector →
      ∀ n : ℕ, 0 < n →
        area n =
            (8 * (n : ℚ) ^ 2 - 5 * (n : ℚ) + 9) /
                (4 * (n : ℚ) ^ 2) -
              2 ^ (1 - n : ℤ) / (n : ℚ) ^ 2 ∧
          area n ≤ 2

end

end MathlibPlus.Open.ResearchFormalization.R3709Claim47856
