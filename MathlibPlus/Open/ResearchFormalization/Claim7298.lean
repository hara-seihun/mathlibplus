import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

/-- The interior entries of a two-endpoint commutator displacement vanish. -/
def fullInteriorBlockVanishes
    (n : ℕ) (J C : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∃ u₀ u₁ : Fin n → ℝ,
      J * C - C * J =
        (fun i j : Fin n =>
          ((if i.val = 0 then (1 : ℝ) else 0) * u₀ j -
            u₀ i * (if j.val = 0 then (1 : ℝ) else 0)) +
          ((if i.val = n - 1 then (1 : ℝ) else 0) * u₁ j -
            u₁ i * (if j.val = n - 1 then (1 : ℝ) else 0)))) →
    ∀ i j : Fin n,
      0 < i.val → i.val < n - 1 →
      0 < j.val → j.val < n - 1 →
      (J * C - C * J) i j = 0

end MathlibPlus.Open.ResearchFormalization
