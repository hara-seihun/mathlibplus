import MathlibPlus.Basic

namespace MathlibPlus.GraphTheory

/-- A nonempty module has a complete/anticomplete partition of its outside. -/
theorem module_outside_partition_claim3350
    {α : Type*} (Adj : α → α → Prop) {M : Set α} (hM : M.Nonempty)
    (hmodule : ∀ v, v ∉ M → ∀ x ∈ M, ∀ y ∈ M, Adj v x ↔ Adj v y) :
    let A : Set α := {v | v ∉ M ∧ ∀ x ∈ M, Adj v x}
    let B : Set α := {v | v ∉ M ∧ ∀ x ∈ M, ¬ Adj v x}
    A ∪ B = Mᶜ ∧ Disjoint A B := by
  let A : Set α := {v | v ∉ M ∧ ∀ x ∈ M, Adj v x}
  let B : Set α := {v | v ∉ M ∧ ∀ x ∈ M, ¬ Adj v x}
  change A ∪ B = Mᶜ ∧ Disjoint A B
  have hcover : ∀ v, v ∉ M → v ∈ A ∪ B := by
    intro v hv
    obtain ⟨x₀, hx₀⟩ := hM
    by_cases h : Adj v x₀
    · left
      exact ⟨hv, fun x hx => (hmodule v hv x hx x₀ hx₀).mpr h⟩
    · right
      exact ⟨hv, fun x hx hAdj => h ((hmodule v hv x hx x₀ hx₀).mp hAdj)⟩
  constructor
  · ext v
    constructor
    · intro hv
      rcases hv with hv | hv
      · exact hv.1
      · exact hv.1
    · intro hv
      exact hcover v hv
  · refine Set.disjoint_left.2 ?_
    intro v hvA hvB
    obtain ⟨x₀, hx₀⟩ := hM
    exact hvB.2 x₀ hx₀ (hvA.2 x₀ hx₀)

end MathlibPlus.GraphTheory
