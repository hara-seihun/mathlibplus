import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R0504Claim26019

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

private def quinticResidual
    (h k l : ℕ → ℚ) (t : ℕ) : ℚ :=
  k t + 2 * l t

private def cubicResidual
    (N : ℕ) (h k l : ℕ → ℚ) (t : ℕ) : ℚ :=
  h t + 3 * k t + k (N - t) + 6 * l t

private def normalizedMiddle
    (N : ℕ) (h k l : ℕ → ℚ) : Prop :=
  ∀ t : ℕ, t ≤ N →
    quinticResidual h k l t = 0 ∧ cubicResidual N h k l t = 0

/-- Claim 26019: once the normalized cubic and quintic lower-block residuals
    vanish in the exact folded eight-factor annihilator carrier, the remaining
    middle functions are `k=-2l` and `h=2l` on the fixed-total interval. -/
def claim26019_normalizedMiddleReduction : Prop :=
  ∀ (N : ℕ) (f h k l : ℕ → ℚ),
    8 ≤ N →
      eightFactorAnnihilator N f h k l →
        normalizedMiddle N h k l →
          ∀ t : ℕ, t ≤ N →
            k t = (-2 : ℚ) * l t ∧ h t = 2 * l t

end MathlibPlus.Open.ResearchFormalization.R0504Claim26019
