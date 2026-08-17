import Mathlib
import MathlibPlus.Open.ResearchFormalization.BatchR0504Claim26022
import MathlibPlus.Open.ResearchFormalization.BatchR0504Claims26023_26024

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R0504LowerBlocks

noncomputable section

private abbrev Eight := Fin 8

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

private def reflectiveOn (N : ℕ) (l : ℕ → ℚ) : Prop :=
  ∀ t : ℕ, t ≤ N → l t = l (N - t)

private def eightFactorAnnihilator
    (N : ℕ) (f h k l : ℕ → ℚ) : Prop :=
  reflectiveOn N l ∧
    ∀ μ : Eight → ℕ,
      (∑ i : Eight, μ i) = N →
        eightFactorEquation N f h k l μ = 0

private def cubicPairExpression
    (N : ℕ) (h k l : ℕ → ℚ) (t : ℕ) : ℚ :=
  h t + 3 * k t + k (N - t) + 6 * l t

private def subsetSumFunctional
    (N : ℕ) (l : ℕ → ℚ) (j : ℕ) (μ : Eight → ℕ) : ℚ :=
  ∑ S ∈ (Finset.univ : Finset Eight).powerset.filter
      (fun S => S.card = j),
    l (foldedFourIndex N (∑ i ∈ S, μ i))

private def middleResidual
    (N : ℕ) (l : ℕ → ℚ) (μ : Eight → ℕ) : ℚ :=
  subsetSumFunctional N l 4 μ - 2 * subsetSumFunctional N l 3 μ +
    2 * subsetSumFunctional N l 2 μ - 2 * subsetSumFunctional N l 1 μ

/-- Claim 26016: with the exact eight-factor annihilator antecedent, the
quadratic direction removed from the lower block leaves the displayed cubic
pair functional, represented by a polynomial of degree at most three. -/
def claim26016_cubicLowerBlockDirection : Prop :=
  ∀ (N : ℕ) (f h k l : ℕ → ℚ),
    8 ≤ N →
      eightFactorAnnihilator N f h k l →
        ∃ p₃ : Polynomial ℚ,
          p₃.natDegree ≤ 3 ∧
            ∀ t : ℕ, t ≤ N →
              p₃.eval (t : ℚ) = cubicPairExpression N h k l t

/-- Claim 26020: after the exact normalized-middle relations are imposed on
an eight-factor annihilator, the four-subset residual is constant on every
fixed-total composition layer. -/
def claim26020_fourSubsetMiddleResidual : Prop :=
  ∀ (N : ℕ) (f h k l : ℕ → ℚ),
    8 ≤ N →
      eightFactorAnnihilator N f h k l →
        (∀ t : ℕ, t ≤ N →
          k t = -2 * l t ∧ h t = 2 * l t) →
          ∀ μ ν : Eight → ℕ,
            (∑ i : Eight, μ i) = N →
              (∑ i : Eight, ν i) = N →
                middleResidual N l μ = middleResidual N l ν

end

end MathlibPlus.Open.ResearchFormalization.R0504LowerBlocks
