import MathlibPlus.Basic

namespace MathlibPlus.LinearAlgebra.Claim17770

/-- The augmented-jet reflection `(v,t) ↦ (v - 2 t c, -t)` in coordinates. -/
noncomputable def augmentedJetReflection (N : ℕ) (c : Fin N → ℝ) :
    (Fin N → ℝ) × ℝ → (Fin N → ℝ) × ℝ :=
  fun z => (z.1 - (2 * z.2) • c, -z.2)

theorem augmentedJetReflection_sq (N : ℕ) (c : Fin N → ℝ)
    (z : (Fin N → ℝ) × ℝ) :
    augmentedJetReflection N c (augmentedJetReflection N c z) = z := by
  rcases z with ⟨v, t⟩
  apply Prod.ext
  · funext i
    simp [augmentedJetReflection]
  · simp [augmentedJetReflection]

end MathlibPlus.LinearAlgebra.Claim17770
