import Mathlib

namespace MathlibPlus.Open.Algebra

/--
The geometric polynomial and its monic reverse have the stated root locations
and factorizations.  The geometric-sum presentation is used at the singular
point of the displayed quotient; away from that point it is the usual
geometric quotient.
-/
def geometricAndReversedRootLocations : Prop :=
  ∀ m : ℕ, 1 ≤ m →
    let a : ℂ := (1 : ℂ) / (Real.sqrt 2 : ℂ)
    let F : ℂ → ℂ := fun x =>
      Finset.sum (Finset.range (m + 1)) (fun k => a ^ k * x ^ k)
    let H : ℂ → ℂ := fun x =>
      Finset.sum (Finset.range (m + 1)) (fun k => a ^ k * x ^ (m - k))
    (∀ x : ℂ, a * x ≠ 1 →
        F x = (1 - (a * x) ^ (m + 1)) / (1 - a * x)) ∧
      (∃ ω : Fin m → ℂ,
        Function.Injective ω ∧
          (∀ j : Fin m,
            ω j ^ (m + 1) = 1 ∧
              ω j ≠ 1 ∧
              ‖a⁻¹ * ω j‖ = Real.sqrt 2) ∧
          (∀ x : ℂ, F x = 0 ↔ ∃ j : Fin m, x = a⁻¹ * ω j)) ∧
      (∃ α : Fin m → ℂ,
        Function.Injective α ∧
          (∀ j : Fin m,
            H (α j) = 0 ∧
              ‖α j‖ = 1 / Real.sqrt 2) ∧
          (∀ x : ℂ, H x = 0 ↔ ∃ j : Fin m, x = α j) ∧
          (∀ x : ℂ,
            H x = Finset.prod Finset.univ (fun j : Fin m => x - α j)) ∧
          (∀ x : ℂ,
            F x = Finset.prod Finset.univ
              (fun j : Fin m => 1 - star (α j) * x)))

end MathlibPlus.Open.Algebra
