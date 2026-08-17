import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R2777Claim35772

noncomputable section
open scoped BigOperators

private def dyadicWeight (j : ℕ) : ℝ :=
  (j : ℝ) / (2 : ℝ) ^ j

private def finiteRepresentation (target : ℕ) (support : Finset ℕ) : Prop :=
  (∑ j ∈ support, dyadicWeight j) = dyadicWeight target

/-- Claim 35772: the two initial weighted targets have the displayed finite
binary witness, including the representation relation between the support and
its target. -/
def claim_35772_initialFiniteWitness : Prop :=
  dyadicWeight 1 = 1 / 2 ∧
    dyadicWeight 2 = 1 / 2 ∧
      finiteRepresentation 1 ({4, 5, 6} : Finset ℕ) ∧
        finiteRepresentation 2 ({4, 5, 6} : Finset ℕ) ∧
          (∑ j ∈ ({4, 5, 6} : Finset ℕ), dyadicWeight j) = 1 / 2

end

end MathlibPlus.Open.ResearchFormalization.R2777Claim35772
