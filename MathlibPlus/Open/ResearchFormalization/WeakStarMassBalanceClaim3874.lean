import Mathlib

open scoped BigOperators Topology
open Filter MeasureTheory

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization

def weakStarZeroOnInterval (a b : ℝ) (r : ℕ → ℝ → ℝ) : Prop :=
  ∀ f : ℝ → ℝ, ContinuousOn f (Set.Icc a b) →
    Tendsto
      (fun j => ∫ x in Set.Icc a b, f x * r j x)
      atTop (𝓝 0)

def positiveMass (a b : ℝ) (r : ℕ → ℝ → ℝ) (j : ℕ) : ℝ :=
  ∫ x in Set.Icc a b, max (r j x) 0

def negativeMass (a b : ℝ) (r : ℕ → ℝ → ℝ) (j : ℕ) : ℝ :=
  ∫ x in Set.Icc a b, max (-(r j x)) 0

def l1Mass (a b : ℝ) (r : ℕ → ℝ → ℝ) (j : ℕ) : ℝ :=
  ∫ x in Set.Icc a b, |r j x|

def weakStarMassBalance_claim3874
    (a b : ℝ) (r : ℕ → ℝ → ℝ) : Prop :=
  (a ≤ b ∧
      (∀ j, IntegrableOn (r j) (Set.Icc a b) volume) ∧
      weakStarZeroOnInterval a b r) →
    (Tendsto
        (fun j => positiveMass a b r j - negativeMass a b r j)
        atTop (𝓝 0) ∧
      (0 < Filter.liminf (fun j => l1Mass a b r j) atTop →
        ∃ ε : ℝ, 0 < ε ∧
          ∀ᶠ j in atTop,
            ε ≤ positiveMass a b r j ∧ ε ≤ negativeMass a b r j))

end MathlibPlus.Open.ResearchFormalization
