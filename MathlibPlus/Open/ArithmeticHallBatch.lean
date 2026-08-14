import Mathlib

noncomputable section

open scoped Matrix

namespace MathlibPlus.Open.ArithmeticHallBatch

/-- Claim 7083: the Jordan relation has only degenerate invariant symmetric forms,
while the scalar Frobenius admits positive invariant forms. -/
def claim_7083 : Prop :=
  let Frel : Matrix (Fin 2) (Fin 2) ℝ := fun i j =>
    if i = 0 ∧ j = 0 then -3
    else if i = 0 ∧ j = 1 then 1
    else if i = 1 ∧ j = 1 then -3
    else 0
  let F9 : Matrix (Fin 2) (Fin 2) ℝ := fun i j =>
    if i = j then -3 else 0
  let PosDef : Matrix (Fin 2) (Fin 2) ℝ → Prop := fun P =>
    P.transpose = P ∧
      ∀ v : Fin 2 → ℝ, v ≠ 0 → 0 < dotProduct v (P.mulVec v)
  (∀ P : Matrix (Fin 2) (Fin 2) ℝ,
      P.transpose = P →
      Frel.transpose * P * Frel = (9 : ℝ) • P →
      (∃ w : ℝ,
        P 0 0 = 0 ∧ P 0 1 = 0 ∧ P 1 0 = 0 ∧ P 1 1 = w) ∧
        ¬ PosDef P) ∧
    (∃ P : Matrix (Fin 2) (Fin 2) ℝ,
      PosDef P ∧ (F9.transpose * P * F9 = (9 : ℝ) • P))

end MathlibPlus.Open.ArithmeticHallBatch
