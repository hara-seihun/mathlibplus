import Mathlib

/-!
# Completed-zeta Loewner positivity through order five

Registry statement for admitted claim 213.  The completed source and all
quantifiers are expanded locally so that the node does not depend on a
not-yet-admitted helper definition.
-/

namespace MathlibPlus.Open.Analysis.CompletedZeta

/-- The completed-zeta order-five positivity claim, including its finite-node
consequence, first-failure lower bound, and the three certified coverage
ranges used by the source. -/
noncomputable def globalOrderFivePositivity : Prop :=
  let xi : ℝ → ℝ := fun s =>
    (((1 / 2 : ℂ) * (s : ℂ) * ((s : ℂ) - 1) *
      completedRiemannZeta (s : ℂ))).re
  let logarithmicDerivative : ℝ → ℝ := fun r => deriv xi r / xi r
  let H : ℝ → ℝ := fun x => logarithmicDerivative (Real.sqrt x) / Real.sqrt x
  let C : (n : ℕ) → ℝ → Matrix (Fin n) (Fin n) ℝ := fun n x i j =>
    (-1 : ℝ) ^ ((i : ℕ) + (j : ℕ) + 1) *
      iteratedDeriv ((i : ℕ) + (j : ℕ) + 1) H x /
        (((i : ℕ) + (j : ℕ) + 1).factorial : ℝ)
  let dividedDifference : ℝ → ℝ → ℝ := fun x y =>
    if x = y then deriv H x else (H x - H y) / (x - y)
  let negativeLoewner : (n : ℕ) → (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ :=
    fun n x i j => -dividedDifference (x i) (x j)
  let HasFailure : ℕ → Prop := fun n =>
    ∃ x : Fin n → ℝ,
      (∀ i, (1 : ℝ) / 4 < x i) ∧ ¬Matrix.PosSemidef (negativeLoewner n x)
  let IsFirstFailure : ℕ → Prop := fun n =>
    HasFailure n ∧ ∀ m < n, ¬HasFailure m
  (∀ x : ℝ, (1 : ℝ) / 4 < x → Matrix.PosDef (C 5 x)) ∧
  (∀ x : Fin 5 → ℝ,
    (∀ i, (1 : ℝ) / 4 < x i) → Matrix.PosSemidef (negativeLoewner 5 x)) ∧
  (∀ n : ℕ, IsFirstFailure n → 6 ≤ n) ∧
  (∀ x : ℝ, x ∈ Set.Icc ((1 : ℝ) / 4) 1260 → Matrix.PosDef (C 5 x)) ∧
  (∀ r : ℝ, r ∈ Set.Icc ((3549 : ℝ) / 100) 100 → Matrix.PosDef (C 5 (r ^ 2))) ∧
  (∀ r : ℝ, 100 ≤ r → Matrix.PosDef (C 5 (r ^ 2)))

end MathlibPlus.Open.Analysis.CompletedZeta
