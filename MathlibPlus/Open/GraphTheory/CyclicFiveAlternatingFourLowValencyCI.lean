import Mathlib.Combinatorics.SimpleGraph.Cayley
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.Data.ZMod.Basic

namespace MathlibPlus.Open.GraphTheory

/-- Cell P1, first order-sixty slice: every ordinary undirected Cayley graph on
`C₅ × A₄` of valency at most fourteen, or complementary valency at least
forty-five, is a CI-graph. -/
def cyclicFiveAlternatingFourLowAndComplementaryValencyCI : Prop :=
  let G := Multiplicative (ZMod 5) × alternatingGroup (Fin 4)
  ∀ S T : Set G,
    S = S⁻¹ →
    T = T⁻¹ →
    1 ∉ S →
    1 ∉ T →
    (Set.ncard S ≤ 14 ∨ 45 ≤ Set.ncard S) →
    (Set.ncard T ≤ 14 ∨ 45 ≤ Set.ncard T) →
    Nonempty (SimpleGraph.mulCayley S ≃g SimpleGraph.mulCayley T) →
      ∃ α : G ≃* G, α '' S = T

end MathlibPlus.Open.GraphTheory
