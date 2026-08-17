import MathlibPlus.Open.ResearchFormalization.Batch_52e47c1f_Frobenius21Support

namespace MathlibPlus.Open.ResearchFormalization.Batch_Frobenius21Structure

open MathlibPlus.Open.ResearchFormalizationBatch.Frobenius21Claims

abbrev CyclicSeven := Multiplicative (ZMod 7)
abbrev CyclicThree := Multiplicative (ZMod 3)

/-- Claim 39588: the verified concrete Frobenius-21 carrier is the
nonabelian semidirect product of cyclic groups of orders seven and three,
with the C₃ generator acting on C₇ by an automorphism of order three. -/
def claim39588 : Prop :=
  ∃ action : CyclicThree →* MulAut CyclicSeven,
    orderOf (action (Multiplicative.ofAdd (1 : ZMod 3))) = 3 ∧
      Nat.card Frobenius21 = 21 ∧
      (∃ x y : Frobenius21, x * y ≠ y * x) ∧
      Nonempty (Frobenius21 ≃* (CyclicSeven ⋊[action] CyclicThree))

end MathlibPlus.Open.ResearchFormalization.Batch_Frobenius21Structure
