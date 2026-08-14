import Mathlib

noncomputable section
open scoped BigOperators

namespace MathlibPlus.Open.ResearchBatchMisc

/-- A three-part partition with no singleton and no part above half the total. -/
def balancedThreePartComponentRegime (n : ℕ) (parts : Fin 3 → ℕ) : Prop :=
  (∑ j : Fin 3, parts j = n) ∧
    (∀ j : Fin 3, 2 ≤ parts j ∧ parts j ≤ n / 2) ∧
      (∀ i j : Fin 3, i.val < j.val → parts j ≤ parts i)

def autocorrelation {f : ℝ → ℝ} (ℓ : ℝ) : ℝ :=
  ∫ x : ℝ, f (x + ℓ) * f x

def jumpEnergy {f : ℝ → ℝ} (ℓ : ℝ) : ℝ :=
  ∫ x : ℝ, |f (x + ℓ) - f x| ^ 2

def realL2Squared {f : ℝ → ℝ} : ℝ :=
  ∫ x : ℝ, f x ^ 2

def autocorrelationAndJumpEnergyIdentity : Prop :=
  ∀ (f : ℝ → ℝ), HasCompactSupport f →
    (∀ ℓ : ℝ, autocorrelation (f := f) ℓ = autocorrelation (f := f) (-ℓ)) ∧
      autocorrelation (f := f) 0 = realL2Squared (f := f) ∧
        (∀ ℓ : ℝ,
          jumpEnergy (f := f) ℓ =
              2 * realL2Squared (f := f) -
                2 * autocorrelation (f := f) ℓ ∧
            0 ≤ jumpEnergy (f := f) ℓ)

end MathlibPlus.Open.ResearchBatchMisc
