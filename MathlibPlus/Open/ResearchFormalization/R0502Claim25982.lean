import MathlibPlus.Open.Algebra.WeightedAlphabetSevenClaim26001

namespace MathlibPlus.Open.ResearchFormalization.R0502Claim25982

noncomputable section

open MathlibPlus.Open.Algebra.WeightedAlphabetSevenClaim26001

/-- The singleton functional obtained from a seven-factor annihilator. -/
def singletonFunctional (N : ℕ) (f h k : Index N → ℚ)
    (t : Index N) : ℚ :=
  f t + 4 * h t + h (reflectIndex N t) +
    6 * k t + 4 * k (reflectIndex N t)

/-- Claim 25982: on the N≥7 fixed-total seven-part composition carrier, the
singleton functional is affine, with the corresponding affine-minus-lower-block
formula for the singleton function. -/
def claim25982 : Prop :=
  ∀ (N : ℕ), 7 ≤ N →
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

end MathlibPlus.Open.ResearchFormalization.R0502Claim25982
