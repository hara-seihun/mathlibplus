import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.BatchR0504Claim26022

private abbrev Eight := Fin 8

private def mixedEight (l : ℕ → ℚ) (μ : Eight → ℕ) : ℚ :=
  ∑ S ∈ (Finset.univ : Finset Eight).powerset,
    (-1 : ℚ) ^ (8 - S.card) *
      l (∑ i ∈ S, μ i)

private def reflectiveOn (N : ℕ) (l : ℕ → ℚ) : Prop :=
  ∀ t : ℕ, t ≤ N → l t = l (N - t)

private def fixedTotalEightfoldDifference (N : ℕ) (l : ℕ → ℚ) : Prop :=
  ∀ μ : Eight → ℕ,
    (∑ i : Eight, μ i) = N →
      mixedEight l μ = 0

private def reflectiveSexticValue
    (d : Fin 4 → ℚ) (N t : ℕ) : ℚ :=
  d 0 +
    d 1 * ((t : ℚ) * (N - t : ℕ)) +
    d 2 * ((t : ℚ) * (N - t : ℕ)) ^ 2 +
    d 3 * ((t : ℚ) * (N - t : ℕ)) ^ 3

/-- Claim 26022: the exact reflective fixed-total eightfold-difference
carrier consists uniquely of the displayed sextics in z=t(N-t). -/
def claim26022_reflectiveEightfoldSolutionsAreSextic : Prop :=
  ∀ (N : ℕ) (l : ℕ → ℚ),
    8 ≤ N →
    reflectiveOn N l →
    fixedTotalEightfoldDifference N l →
      ∃! d : Fin 4 → ℚ,
        ∀ t : ℕ, t ≤ N →
          l t = reflectiveSexticValue d N t

end MathlibPlus.Open.ResearchFormalization.BatchR0504Claim26022
