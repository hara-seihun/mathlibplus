import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace MathlibPlus.Algebra.Claim29363

/-!
Formalization of admitted claim 29363 (packet `R-0498`).  The finite domain
`{0, ..., N}` is represented exactly by `Fin (N + 1)`; no values outside the
stated domain occur in the hypotheses or conclusions.
-/

/-- Every fixed-total three-term annihilator is affine on its stated domain. -/
theorem compositionAnnihilator_affine
    (N : ℕ) (hN : 1 ≤ N) (f : Fin (N + 1) → ℚ)
    (h : ∀ a b c : Fin (N + 1), a.val + b.val + c.val = N →
      f a + f b + f c = 0) :
    ∃ δ : ℚ,
      (∀ j : Fin (N + 1), f j = f 0 + (j.val : ℚ) * δ) ∧
        3 * f 0 + (N : ℚ) * δ = 0 := by
  let δ : ℚ := f ⟨1, by omega⟩ - f 0
  have hstep : ∀ j : Fin N, f j.succ = f j.castSucc + δ := by
    intro j
    let k : Fin (N + 1) := ⟨N - j.val - 1, by omega⟩
    have h₁ := h j.castSucc ⟨1, by omega⟩ k (by simp [k]; omega)
    have h₂ := h j.succ 0 k (by simp [k]; omega)
    dsimp [δ]
    linarith
  have hform : ∀ j : Fin (N + 1),
      f j = f 0 + (j.val : ℚ) * δ := by
    intro j
    induction j using Fin.induction with
    | zero => simp
    | succ j ih =>
        rw [hstep j, ih]
        simp only [Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]
        ring
  refine ⟨δ, hform, ?_⟩
  have h₀ := h 0 0 (Fin.last N) (by simp)
  have hNform : f (Fin.last N) = f 0 + (N : ℚ) * δ := by
    simpa using hform (Fin.last N)
  linarith

/-- The affine parameter in the preceding representation is unique. -/
theorem compositionAnnihilator_affine_parameter_unique
    (N : ℕ) (hN : 1 ≤ N) (f : Fin (N + 1) → ℚ)
    (δ₁ δ₂ : ℚ)
    (h₁ : ∀ j : Fin (N + 1), f j = f 0 + (j.val : ℚ) * δ₁)
    (h₂ : ∀ j : Fin (N + 1), f j = f 0 + (j.val : ℚ) * δ₂) :
    δ₁ = δ₂ := by
  have h₁' : f ⟨1, by omega⟩ = f 0 + δ₁ := by
    simpa using h₁ ⟨1, by omega⟩
  have h₂' : f ⟨1, by omega⟩ = f 0 + δ₂ := by
    simpa using h₂ ⟨1, by omega⟩
  linarith

/-- Conversely, the displayed affine data satisfy the fixed-total equation. -/
theorem affine_composition_satisfies
    (N : ℕ) (δ b₀ : ℚ)
    (hconstraint : 3 * b₀ + (N : ℚ) * δ = 0) :
    ∀ a b c : Fin (N + 1), a.val + b.val + c.val = N →
      (b₀ + (a.val : ℚ) * δ) + (b₀ + (b.val : ℚ) * δ) +
          (b₀ + (c.val : ℚ) * δ) = 0 := by
  intro a b c hab
  have hcast : (a.val : ℚ) + (b.val : ℚ) + (c.val : ℚ) = (N : ℚ) := by
    exact_mod_cast hab
  calc
    (b₀ + (a.val : ℚ) * δ) + (b₀ + (b.val : ℚ) * δ) +
          (b₀ + (c.val : ℚ) * δ) =
        3 * b₀ + ((a.val : ℚ) + (b.val : ℚ) + (c.val : ℚ)) * δ := by ring
    _ = 3 * b₀ + (N : ℚ) * δ := by rw [hcast]
    _ = 0 := hconstraint

end MathlibPlus.Algebra.Claim29363
