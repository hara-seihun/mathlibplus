import MathlibPlus.Basic

namespace MathlibPlus.Combinatorics.Claim43041

/-- The numerical factors in the one-unbalanced raw census are represented by
finite choice types.  The source-specific identification with Q60 connection
sets is intentionally not reconstructed here. -/
theorem rawCensusArithmetic :
    let RotationState := Fin 7 × Bool × (Fin 6 → Bool)
    let ReflectionSubset := Finset (Fin 15)
    let CentralBit := Bool
    Fintype.card RotationState = 896 ∧
      Fintype.card ReflectionSubset = 2 ^ 15 ∧
      Fintype.card CentralBit = 2 ∧
      Fintype.card (CentralBit × RotationState × ReflectionSubset) = 58720256 := by
  dsimp
  have hrot : Fintype.card (Fin 7 × Bool × (Fin 6 → Bool)) = 896 := by
    simp [Fintype.card_prod, Fintype.card_fun]
  have href : Fintype.card (Finset (Fin 15)) = 2 ^ 15 := by
    rw [Fintype.card_finset, Fintype.card_fin]
  constructor
  · exact hrot
  constructor
  · exact href
  constructor
  · simp
  · rw [Fintype.card_prod, Fintype.card_prod, hrot, href]
    simp

end MathlibPlus.Combinatorics.Claim43041
