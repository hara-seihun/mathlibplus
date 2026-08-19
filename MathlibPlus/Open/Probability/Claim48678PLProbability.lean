import Mathlib

namespace MathlibPlus.Open.Probability.Claim48678

open scoped BigOperators

/-- Total positive rate of three labels. -/
def totalRate48678 (x : Fin 3 → ℝ) : ℝ :=
  ∑ i : Fin 3, x i

/-- The sequential persistent Plackett--Luce probability of an actual order,
with each denominator summing the rates of labels not yet selected. -/
noncomputable def persistentPLProbability48678
    (x : Fin 3 → ℝ) (π : Equiv.Perm (Fin 3)) : ℝ :=
  ∏ k : Fin 3,
    x (π k) /
      ∑ j : Fin 3,
        if (π.symm j).val ≥ k.val then x j else 0

/-- Claim 48678: the probability of the order `(i,j,k)` is the first-choice
factor times the second-choice factor, with total rate `S`. -/
noncomputable def claim48678_threeLabelPLProbability : Prop :=
  ∀ (x : Fin 3 → ℝ) (π : Equiv.Perm (Fin 3)),
    (∀ i : Fin 3, 0 < x i) →
      persistentPLProbability48678 x π =
        (x (π 0) / totalRate48678 x) *
          (x (π 1) / (totalRate48678 x - x (π 0)))

end MathlibPlus.Open.Probability.Claim48678
