import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.ExponentialRigidity

open scoped BigOperators

noncomputable section

def dividedDifferenceCoefficient (lam : Fin 3 → ℝ) (i : Fin 3) : ℝ :=
  Finset.prod (Finset.univ.erase i) (fun j => (lam i - lam j))⁻¹

def secondDividedDifference (lam : Fin 3 → ℝ) (mu : ℝ) : ℝ :=
  Finset.sum Finset.univ
    (fun i : Fin 3 => Real.exp (lam i * mu) * dividedDifferenceCoefficient lam i)

def claim_24601 : Prop :=
  ∀ (lam : Fin 3 → ℝ) (c : Fin 3 → ℝ) (mu : ℝ),
    Function.Injective lam →
    (∀ i : Fin 3, c i ≠ 0) →
    (Finset.sum Finset.univ c = 0) →
    (Finset.sum Finset.univ (fun i : Fin 3 => c i * lam i) = 0) →
    mu ≠ 0 →
      (Finset.sum Finset.univ
          (fun i : Fin 3 => c i * Real.exp (lam i * mu)) ≠ 0) ∧
      (∃ a : ℝ, a ≠ 0 ∧
        (∀ i : Fin 3, c i = a * dividedDifferenceCoefficient lam i) ∧
        (Finset.sum Finset.univ
            (fun i : Fin 3 => c i * Real.exp (lam i * mu))) =
          a * secondDividedDifference lam mu)

end

end MathlibPlus.Open.ResearchFormalization.ExponentialRigidity
