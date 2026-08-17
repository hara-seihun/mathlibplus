import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R0521Claim22282

/-- A bounded interval contains only finitely many indices of a static train. -/
def noFiniteAccumulation (x : ℤ → ℝ) : Prop :=
  ∀ (a b : ℝ), {i : ℤ | a ≤ x i ∧ x i ≤ b}.Finite

/-- The consecutive gap of a static zero configuration. -/
def gap (x : ℤ → ℝ) (i : ℤ) : ℝ :=
  x (i + 1) - x i

/-- Claim 22282: the normalized cumulative symmetric gap profile.  `E` is
    retained as the profile value rather than being hidden in a definitional
    wrapper, and the gaps are the consecutive differences of the supplied
    zero configuration. -/
def normalizedCumulativeSymmetricGapProfile_claim22282
    (x : ℤ → ℝ) (k : ℤ) (r : ℕ) (E : ℝ) : Prop :=
  StrictMono x →
    noFiniteAccumulation x →
      1 ≤ r →
        E = (1 / gap x k) *
          ∑ j ∈ Finset.Icc 1 r,
            (gap x (k - (j : ℤ)) + gap x (k + (j : ℤ)) - 2 * gap x k)

end MathlibPlus.Open.ResearchFormalization.R0521Claim22282
