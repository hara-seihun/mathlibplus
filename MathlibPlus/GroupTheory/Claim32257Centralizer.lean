import Mathlib.GroupTheory.Subgroup.Centralizer

namespace MathlibPlus.GroupTheory

/-- Claim 32257: a sharply transitive abelian subgroup of the permutation
 group on `B` is equal to its centralizer in `Sym(B)`. -/
theorem claim32257_centralizer_of_regular_abelian_permutation_group
    {B : Type*} (G : Subgroup (Equiv.Perm B)) (x₀ : B)
    (hreg : ∀ x y : B, ∃! g : G, (g : Equiv.Perm B) x = y)
    (hab : ∀ g h : G, (g : Equiv.Perm B) * h = h * g) :
    Subgroup.centralizer (G : Set (Equiv.Perm B)) = G := by
  apply le_antisymm
  · intro σ hσ
    obtain ⟨g, hgx₀, _⟩ := hreg x₀ (σ x₀)
    have hσ_eq : σ = (g : Equiv.Perm B) := by
      ext x
      obtain ⟨h, hhx, _⟩ := hreg x₀ x
      calc
        σ x = σ ((h : Equiv.Perm B) x₀) := by rw [hhx]
        _ = (σ * (h : Equiv.Perm B)) x₀ := rfl
        _ = ((h : Equiv.Perm B) * σ) x₀ := by
          rw [← (Subgroup.mem_centralizer_iff.mp hσ) (h : Equiv.Perm B) h.property]
        _ = (h : Equiv.Perm B) (σ x₀) := rfl
        _ = (h : Equiv.Perm B) ((g : Equiv.Perm B) x₀) := by rw [hgx₀]
        _ = ((h : Equiv.Perm B) * (g : Equiv.Perm B)) x₀ := rfl
        _ = ((g : Equiv.Perm B) * (h : Equiv.Perm B)) x₀ := by
          rw [hab h g]
        _ = (g : Equiv.Perm B) ((h : Equiv.Perm B) x₀) := rfl
        _ = (g : Equiv.Perm B) x := by rw [hhx]
    rw [hσ_eq]
    exact g.property
  · intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact hab ⟨h, hh⟩ ⟨g, hg⟩

end MathlibPlus.GroupTheory
