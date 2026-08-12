import MathlibPlus.Basic

namespace MathlibPlus.Analysis.Claim37963

/-!
The source's periodic derivative carrier is not otherwise defined in the
claim record.  This theorem retains the period premise, defines the displayed
Delta/Gamma/r/phi/D formulas literally over `ℚ`, and writes `phi_k⁻¹` as the
explicit affine inverse valid under `h k ≠ 0`.
-/

/-- The displayed shifted derivative is the conjugate affine map. -/
theorem periodic_affine_shift_formula
    (h t : ℕ → ℚ) (d k : ℕ)
    (_hperiodic : ∀ j, h (j + d) = h j)
    (hk : h k ≠ 0) :
    let Δ : ℕ → ℚ := fun j => t (j + d) - t j
    let Γ : ℕ → ℚ := fun j => (-1 : ℚ) ^ j * Δ j
    let r : ℕ → ℚ := fun j => h (j + 1) / h j
    let φ : ℕ → ℚ → ℚ := fun j z => h j * z + Γ j
    let D : ℕ → ℚ → ℚ :=
      fun j z => r j * z + Γ (j + 1) - r j * Γ j
    ∀ z, D k z = φ (k + 1) ((z - Γ k) / h k) := by
  dsimp
  intro z
  field_simp [hk]
  ring

end MathlibPlus.Analysis.Claim37963
