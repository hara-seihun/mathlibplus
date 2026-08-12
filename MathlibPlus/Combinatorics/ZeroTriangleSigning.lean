import Mathlib.Data.ZMod.Basic

namespace MathlibPlus.Combinatorics

/-- A symmetric `𝔽₂`-signing with zero triangle sums is a coboundary. -/
theorem zeroTriangleSigningCoboundary
    {α : Type*} (q₀ : α) (s : α → α → ZMod 2)
    (hdiag : ∀ u, s u u = 0)
    (hsymm : ∀ u v, s u v = s v u)
    (htri : ∀ ⦃u v w : α⦄, u ≠ v → v ≠ w → u ≠ w →
      s u v + s u w + s v w = 0) :
    ∀ ⦃u v : α⦄, u ≠ v → s u v = s q₀ u + s q₀ v := by
  intro u v huv
  by_cases hu : q₀ = u
  · subst hu
    simp [hdiag]
  by_cases hv : q₀ = v
  · subst hv
    rw [hsymm]
    simp [hdiag]
  have hq_u : q₀ ≠ u := hu
  have hq_v : q₀ ≠ v := hv
  have h := htri hq_u huv hq_v
  have h' : s u v + (s q₀ u + s q₀ v) = 0 := by
    simpa [add_assoc, add_comm, add_left_comm] using h
  calc
    s u v = -(s q₀ u + s q₀ v) := eq_neg_of_add_eq_zero_left h'
    _ = s q₀ u + s q₀ v := by simp [add_comm]

end MathlibPlus.Combinatorics
