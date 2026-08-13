import Mathlib

namespace MathlibPlus.Combinatorics.Claim5447

/-- A finite vertex-map acts contravariantly on the rational vertex modules by
pullback. The tree-contraction and tree-specific carriers are not invented
because the packet only specifies the vertex-map action. -/
theorem contravariantVertexPullback_claim5447
    {V W : Type*} [Fintype V] [Fintype W]
    (π : V → W) :
    ∃ πstar : (W → ℚ) →ₗ[ℚ] (V → ℚ),
      ∀ f v, πstar f v = f (π v) := by
  let πstar : (W → ℚ) →ₗ[ℚ] (V → ℚ) :=
    { toFun := fun f v ↦ f (π v)
      map_add' := by
        intro f g
        funext v
        rfl
      map_smul' := by
        intro c f
        funext v
        rfl }
  exact ⟨πstar, by intro f v; rfl⟩

end MathlibPlus.Combinatorics.Claim5447
