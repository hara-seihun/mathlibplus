import MathlibPlus.Open.Algebra.WeightedAlphabetSevenClaim26001

namespace MathlibPlus.Open.ResearchFormalization.R0503Claim25994

open MathlibPlus.Open.Algebra.WeightedAlphabetSevenClaim26001

noncomputable section

def singletonFunctional (N : ℕ)
    (f h k : Index N → ℚ) (t : Index N) : ℚ :=
  f t + 4 * h t + h (reflectIndex N t) +
    6 * k t + 4 * k (reflectIndex N t)

/-- The exact seven-part composition carrier is used for every `N`; no
additional lower bound on `N` is part of the singleton elimination claim. -/
def singletonFunctionalAffineDetermination_claim25994 : Prop :=
  ∀ (N : ℕ),
    ∀ (f h k : Index N → ℚ),
      sevenFactorAnnihilator N f h k →
        ∃ A B : ℚ,
          (∀ t : Index N,
            singletonFunctional N f h k t = A + B * (t.1 : ℚ)) ∧
          (∀ t : Index N,
            f t = A + B * (t.1 : ℚ) -
              4 * h t - h (reflectIndex N t) -
              6 * k t - 4 * k (reflectIndex N t))

end

end MathlibPlus.Open.ResearchFormalization.R0503Claim25994
