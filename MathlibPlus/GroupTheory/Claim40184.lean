import Mathlib.GroupTheory.Perm.Basic

namespace MathlibPlus.GroupTheory.Claim40184

/-- A regular representation of a fixed group is unique up to relabelling of
its underlying set.  The displayed intertwining equation is the subgroup
conjugacy assertion for the two represented copies. -/
theorem regularRepresentations_conjugate
    {H α : Type*} [Group H] [Nonempty α]
    (rho sigma : H →* Equiv.Perm α)
    (hρ : ∀ x y : α, ∃! h : H, rho h x = y)
    (hσ : ∀ x y : α, ∃! h : H, sigma h x = y) :
    ∃ g : Equiv.Perm α, ∀ h : H, ∀ x : α,
      g (rho h x) = sigma h (g x) := by
  classical
  let x₀ : α := Classical.choice (inferInstance : Nonempty α)
  let eρ : H ≃ α :=
    Equiv.ofBijective (fun h : H => rho h x₀) (by
      constructor
      · intro h k hk
        exact (hρ x₀ (rho h x₀)).unique rfl hk.symm
      · intro y
        obtain ⟨h, hh, -⟩ := hρ x₀ y
        exact ⟨h, hh⟩)
  let eσ : H ≃ α :=
    Equiv.ofBijective (fun h : H => sigma h x₀) (by
      constructor
      · intro h k hk
        exact (hσ x₀ (sigma h x₀)).unique rfl hk.symm
      · intro y
        obtain ⟨h, hh, -⟩ := hσ x₀ y
        exact ⟨h, hh⟩)
  let g : Equiv.Perm α := eρ.symm.trans eσ
  have hρ_action (h k : H) : eρ (h * k) = rho h (eρ k) := by
    change rho (h * k) x₀ = rho h (rho k x₀)
    simp [map_mul]
  have hσ_action (h k : H) : eσ (h * k) = sigma h (eσ k) := by
    change sigma (h * k) x₀ = sigma h (sigma k x₀)
    simp [map_mul]
  have hg (k : H) : g (eρ k) = eσ k := by
    simp [g]
  refine ⟨g, ?_⟩
  intro h x
  obtain ⟨k, rfl⟩ := eρ.surjective x
  calc
    g (rho h (eρ k)) = g (eρ (h * k)) := by rw [hρ_action]
    _ = eσ (h * k) := hg (h * k)
    _ = sigma h (eσ k) := hσ_action h k
    _ = sigma h (g (eρ k)) := by rw [hg]

end MathlibPlus.GroupTheory.Claim40184
