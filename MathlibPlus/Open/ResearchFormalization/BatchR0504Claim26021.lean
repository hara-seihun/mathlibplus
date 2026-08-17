import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.BatchR0504Claim26021

open scoped BigOperators

noncomputable section

private abbrev Eight26021 := Fin 8

/-- The sum of l over a prescribed subset of the eight composition parts. -/
def subsetSum26021 (k : ℕ) (l : ℕ → ℚ) (μ : Eight26021 → ℕ) : ℚ :=
  ∑ S ∈ (Finset.univ : Finset Eight26021).powerset.filter
      (fun S => S.card = k),
    l (∑ i ∈ S, μ i)

/-- The fixed-total eightfold mixed difference at zero. -/
def mixedEightfoldDifference26021
    (l : ℕ → ℚ) (μ : Eight26021 → ℕ) : ℚ :=
  ∑ S ∈ (Finset.univ : Finset Eight26021).powerset,
    (-1 : ℚ) ^ (8 - S.card) * l (∑ i ∈ S, μ i)

/-- The pure-middle residual from the four-, three-, two-, and one-subset
blocks. -/
def pureMiddleResidual26021
    (l : ℕ → ℚ) (μ : Eight26021 → ℕ) : ℚ :=
  subsetSum26021 4 l μ - 2 * subsetSum26021 3 l μ +
    2 * subsetSum26021 2 l μ - 2 * subsetSum26021 1 l μ

/-- Reflection on the bounded interval [0,N]. -/
def reflectiveOn26021 (N : ℕ) (l : ℕ → ℚ) : Prop :=
  ∀ t : ℕ, t ≤ N → l t = l (N - t)

/-- Claim 26021: on every fixed-total eight-part composition, complementing
subsets gives the exact mixed-difference identity; fixing the endpoint value
then identifies zero mixed difference with constancy of the pure-middle
residual at -2 l(0). -/
def claim26021 : Prop :=
  ∀ (N : ℕ) (l : ℕ → ℚ),
    reflectiveOn26021 N l →
      (∀ μ : Eight26021 → ℕ,
        (∑ i : Eight26021, μ i) = N →
          mixedEightfoldDifference26021 l μ =
            2 * l 0 + pureMiddleResidual26021 l μ) ∧
        ((∀ μ : Eight26021 → ℕ,
            (∑ i : Eight26021, μ i) = N →
              mixedEightfoldDifference26021 l μ = 0) ↔
          (∀ μ : Eight26021 → ℕ,
            (∑ i : Eight26021, μ i) = N →
              pureMiddleResidual26021 l μ = -2 * l 0))

end

end MathlibPlus.Open.ResearchFormalization.BatchR0504Claim26021
