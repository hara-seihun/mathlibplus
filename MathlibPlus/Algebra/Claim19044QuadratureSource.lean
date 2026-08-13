import Mathlib

namespace MathlibPlus.Algebra.Claim19044

/-- The three support values of the finite rational law in admitted claim
19044, in the source order. -/
def nodeValues_claim19044 : Fin 3 → ℚ := ![5, 1 / 5, 2]

/-- The three probabilities of the finite rational law in admitted claim
19044, in the source order. -/
def nodeWeights_claim19044 : Fin 3 → ℚ := ![1 / 40, 13 / 40, 26 / 40]

/-- Normalized even moments for the displayed finite law. -/
def normalizedEvenMoment_claim19044 (k : ℕ) : ℚ :=
  (∑ i : Fin 3,
      nodeWeights_claim19044 i * nodeValues_claim19044 i ^ (2 * k)) /
    (Nat.factorial (2 * k) : ℚ)

end MathlibPlus.Algebra.Claim19044
