import MathlibPlus.Basic

namespace MathlibPlus.Combinatorics

/-- Exact count of ordered one-card/two-card deletion origins with disjoint
origins in a 15-vertex base. -/
theorem deletionOriginTriples_claim23775 :
    Fintype.card {p : Fin 15 × Finset (Fin 15) //
      p.2.card = 2 ∧ p.1 ∉ p.2} = 15 * Nat.choose 14 2 ∧
      15 * Nat.choose 14 2 = 1365 := by
  native_decide

end MathlibPlus.Combinatorics
