import MathlibPlus.Basic

namespace MathlibPlus.GraphTheory

/-!
Formalization of admitted claim 28917.  `σ` is the permutation representation
of the acting group, `h_two` is two-transitivity on ordered pairs of distinct
vertices, and `h_inv` says that every represented permutation is a graph
automorphism.
-/

/-- A two-transitive graph action leaves only the empty and complete cases. -/
theorem twoTransitiveSimpleGraph
    {V Γ : Type*} [Group Γ] (G : SimpleGraph V)
    (σ : Γ →* Equiv.Perm V)
    (h_two : ∀ x y z w : V, x ≠ y → z ≠ w →
      ∃ g : Γ, σ g x = z ∧ σ g y = w)
    (h_inv : ∀ (g : Γ) (x y : V),
      G.Adj (σ g x) (σ g y) ↔ G.Adj x y) :
    (∀ x y : V, x ≠ y → G.Adj x y) ∨
      (∀ x y : V, x ≠ y → ¬ G.Adj x y) := by
  by_cases h_complete : ∀ x y : V, x ≠ y → G.Adj x y
  · exact Or.inl h_complete
  · right
    have h_exists : ∃ x y : V, x ≠ y ∧ ¬ G.Adj x y := by
      by_contra h
      apply h_complete
      intro x y hxy
      by_contra hAdj
      apply h
      exact ⟨x, y, hxy, hAdj⟩
    obtain ⟨x₀, y₀, hxy₀, hnot⟩ := h_exists
    intro x y hxy
    obtain ⟨g, hgx, hgy⟩ := h_two x₀ y₀ x y hxy₀ hxy
    have hiff : G.Adj x y ↔ G.Adj x₀ y₀ := by
      simpa [hgx, hgy] using h_inv g x₀ y₀
    exact fun hAdj => hnot (hiff.mp hAdj)

end MathlibPlus.GraphTheory
