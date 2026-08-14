import Mathlib

namespace MathlibPlus.Open.Combinatorics

/-- A new closed integer interval is a strict improvement of an old one when
it is contained in, but is not equal to, the old interval. -/
def strictIntervalImprovement (oldInterval newInterval : Set ℤ) : Prop :=
  newInterval ⊆ oldInterval ∧ newInterval ≠ oldInterval

/-- Claim 42204: the three displayed combined intervals are strict
improvements of their degree-four intervals.  The final conjunct records the
resulting failure of the degree-four-is-always-strongest shortcut on this
family. -/
def explicitStrictIntervalImprovements_claim42204 : Prop :=
  strictIntervalImprovement (Set.Icc (210 : ℤ) 280) (Set.Icc (234 : ℤ) 280) ∧
    strictIntervalImprovement (Set.Icc (57297 : ℤ) 81360) (Set.Icc (57297 : ℤ) 66550) ∧
    strictIntervalImprovement (Set.Icc (39299 : ℤ) 65835) (Set.Icc (39299 : ℤ) 53176) ∧
    ¬ (Set.Icc (210 : ℤ) 280 = Set.Icc (234 : ℤ) 280 ∧
      Set.Icc (57297 : ℤ) 81360 = Set.Icc (57297 : ℤ) 66550 ∧
      Set.Icc (39299 : ℤ) 65835 = Set.Icc (39299 : ℤ) 53176)

end MathlibPlus.Open.Combinatorics
