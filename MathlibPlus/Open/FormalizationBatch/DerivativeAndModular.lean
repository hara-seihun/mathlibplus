import Mathlib

open scoped BigOperators
open Set
noncomputable section

namespace MathlibPlus.Open.FormalizationBatch

def claim59682 : Prop :=
  ∃ (S : Set ℝ) (a : ℝ) (f : ℝ → ℝ),
    S.Countable ∧ Dense S ∧ Differentiable ℝ f ∧
      Differentiable ℝ (fun _ : ℝ => (0 : ℝ)) ∧ f a = 0 ∧
        (∀ x ∈ S, deriv f x = deriv (fun _ : ℝ => (0 : ℝ)) x) ∧
      f ≠ (fun _ : ℝ => (0 : ℝ)) ∧ StrictMono f ∧ Function.Bijective f

def claim59746 : Prop :=
  ∀ a : ℝ, ∃ (C : Set ℝ) (f : ℝ → ℝ),
    IsGδ C ∧ Dense C ∧ Differentiable ℝ f ∧
      Differentiable ℝ (fun _ : ℝ => (0 : ℝ)) ∧ f a = 0 ∧
        (∀ x ∈ C, deriv f x = deriv (fun _ : ℝ => (0 : ℝ)) x) ∧
      f ≠ (fun _ : ℝ => (0 : ℝ)) ∧ StrictMono f ∧ Function.Bijective f

def claim59751 : Prop :=
  ∀ (I : Type*) [Fintype I] (q : I → ℂ)
      (a : ℝ → ℂ) (rho : ℂ),
    (∀ i, ‖q i‖ < 1) →
    (∀ x, a x = 0 ↔ x = 0) →
      ((∏ i, (1 - q i)) * a (2 * rho.re - 1) = 0 ↔
        rho.re = 1 / 2)

end MathlibPlus.Open.FormalizationBatch
