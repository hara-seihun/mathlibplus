import MathlibPlus.Basic

namespace MathlibPlus.Combinatorics

/-- Claim 21065: a nonempty finite distinct-set family with the stated
containment, missing-color, and common-core conditions has one member. -/
theorem claim21065_missingColorFiber
    {α : Type*} [DecidableEq α]
    (Q : Finset α) (y : α) (Xℓ : Finset (Finset α))
    (hX : ∀ X ∈ Xℓ, X ⊆ Q ∧ y ∉ X ∧ Q.erase y ⊆ X)
    (hne : Xℓ.Nonempty) :
    (∀ X ∈ Xℓ, X = Q.erase y) ∧
      Xℓ = {Q.erase y} ∧ Xℓ.card = 1 := by
  have hEq : ∀ X ∈ Xℓ, X = Q.erase y := by
    intro X hXm
    obtain ⟨hsub, hy, hcore⟩ := hX X hXm
    apply Finset.Subset.antisymm
    · intro x hx
      have hxQ : x ∈ Q := hsub hx
      have hxy : x ≠ y := by
        intro hxy
        exact hy (hxy ▸ hx)
      exact Finset.mem_erase.mpr ⟨hxy, hxQ⟩
    · exact hcore
  obtain ⟨X₀, hX₀⟩ := hne
  have hcan : Q.erase y ∈ Xℓ := by
    rw [← hEq X₀ hX₀]
    exact hX₀
  have hfamily : Xℓ = {Q.erase y} := by
    ext X
    constructor
    · intro hXm
      rw [hEq X hXm]
      simp
    · intro hsingleton
      have hcanonical : X = Q.erase y := Finset.mem_singleton.mp hsingleton
      rw [hcanonical]
      exact hcan
  refine ⟨hEq, hfamily, ?_⟩
  rw [hfamily]
  simp

/-- Claim 25084: the two displayed finite state counts. -/
theorem claim25084_state_and_triple_counts :
    Nat.choose 8 4 / 2 = 35 ∧ Nat.choose 35 3 = 6545 := by
  norm_num [Nat.choose]

end MathlibPlus.Combinatorics
