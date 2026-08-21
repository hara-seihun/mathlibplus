import Mathlib

namespace MathlibPlus.Open.GraphTheory

/-- Cell P1, four additional order-sixty rows: ordinary undirected Cayley
graphs on `C₅ × A₄` are CI at valencies fifteen through eighteen and their
complementary valencies forty-one through forty-four. -/
def cyclicFiveAlternatingFourValencyFifteenThroughEighteenCI : Prop :=
  let G := Multiplicative (ZMod 5) × alternatingGroup (Fin 4)
  ∀ S T : Set G,
    S = S⁻¹ →
    T = T⁻¹ →
    1 ∉ S →
    1 ∉ T →
    (((15 ≤ Set.ncard S ∧ Set.ncard S ≤ 18) ∨
      (41 ≤ Set.ncard S ∧ Set.ncard S ≤ 44))) →
    (((15 ≤ Set.ncard T ∧ Set.ncard T ≤ 18) ∨
      (41 ≤ Set.ncard T ∧ Set.ncard T ≤ 44))) →
    Nonempty (SimpleGraph.mulCayley S ≃g SimpleGraph.mulCayley T) →
      ∃ α : G ≃* G, α '' S = T

end MathlibPlus.Open.GraphTheory
