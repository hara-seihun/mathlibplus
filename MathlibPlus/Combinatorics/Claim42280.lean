import MathlibPlus.Basic

namespace MathlibPlus.Combinatorics

/-- The concrete four-coordinate families from claim 42280 witness that a
one-element cardinality gap does not force a toggle deletion. -/
theorem nearEqualLayersCounterexample_claim42280 :
    let L : Finset (Finset (Fin 4)) :=
      {(∅ : Finset (Fin 4)), {0, 1, 2}, (Finset.univ : Finset (Fin 4))}
    let U : Finset (Finset (Fin 4)) :=
      {{0, 3}, (Finset.univ : Finset (Fin 4))}
    (∀ A ∈ L, ∀ B ∈ L, A ∪ B ∈ L) ∧
    (∀ A ∈ U, ∀ B ∈ U, A ∪ B ∈ U) ∧
    Finset.univ ∈ L ∧ Finset.univ ∈ U ∧
    (∀ A ∈ L, A = ∅ ∨ 3 ≤ A.card) ∧
    (∀ A ∈ U, 2 ≤ A.card) ∧
    U.card = L.card - 1 ∧
    U ≠ L.erase ∅ := by
  dsimp
  constructor
  · intro A hA B hB
    simp only [Finset.mem_insert, Finset.mem_singleton] at hA hB
    rcases hA with rfl | rfl | rfl <;>
      rcases hB with rfl | rfl | rfl <;>
      simp
  constructor
  · intro A hA B hB
    simp only [Finset.mem_insert, Finset.mem_singleton] at hA hB
    rcases hA with rfl | rfl <;>
      rcases hB with rfl | rfl <;>
      simp
  constructor
  · simp
  constructor
  · simp
  constructor
  · intro A hA
    simp only [Finset.mem_insert, Finset.mem_singleton] at hA
    rcases hA with rfl | rfl | rfl <;> simp
  constructor
  · intro A hA
    simp only [Finset.mem_insert, Finset.mem_singleton] at hA
    rcases hA with rfl | rfl <;> simp
  constructor
  · decide
  · decide

end MathlibPlus.Combinatorics
