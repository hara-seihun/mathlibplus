import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.BatchR0504Claim26014

private abbrev Eight := Fin 8

private def reflectiveOn (N : ℕ) (l : ℕ → ℚ) : Prop :=
  ∀ t : ℕ, t ≤ N → l t = l (N - t)

private def foldedFourIndex (N s : ℕ) : ℕ :=
  min s (N - s)

private def fourBlock (N : ℕ) (l : ℕ → ℚ) (μ : Eight → ℕ) : ℚ :=
  ∑ S ∈ (Finset.univ : Finset Eight).powerset.filter
      (fun S => S.card = 4),
    l (foldedFourIndex N (∑ i ∈ S, μ i))

private def eightFactorEquation
    (N : ℕ) (f h k l : ℕ → ℚ) (μ : Eight → ℕ) : ℚ :=
  (∑ i : Eight, f (μ i)) +
    (∑ i : Eight, ∑ j ∈ Finset.Ioi i, h (μ i + μ j)) +
    (∑ i : Eight, ∑ j ∈ Finset.Ioi i,
      ∑ r ∈ Finset.Ioi j, k (μ i + μ j + μ r)) +
    fourBlock N l μ

private def eightFactorAnnihilator
    (N : ℕ) (f h k l : ℕ → ℚ) : Prop :=
  reflectiveOn N l ∧
    ∀ μ : Eight → ℕ,
      (∑ i : Eight, μ i) = N →
        eightFactorEquation N f h k l μ = 0

/-- Claim 26014: in the exact compressed eight-factor annihilator carrier,
the singleton block is affine after the lower blocks are accounted for. -/
def claim26014_affineSingletonElimination : Prop :=
  ∀ (N : ℕ) (f h k l : ℕ → ℚ),
    8 ≤ N →
      eightFactorAnnihilator N f h k l →
        ∃ (A B : ℚ),
          ∀ t : ℕ,
            t ≤ N →
              f t =
                A + B * (t : ℚ) -
                  5 * h t - h (N - t) -
                    10 * k t - 5 * k (N - t) - 20 * l t

end MathlibPlus.Open.ResearchFormalization.BatchR0504Claim26014
