import MathlibPlus.Open.ResearchFormalizationBatch01_01a000fa

namespace MathlibPlus.Open.ResearchFormalizationBatch01_01a000fa

/-- Claim 42323: the exact finite neutral order and join relation obey the
semilattice laws. -/
def claim42323 : Prop :=
  claim42321 ∧
    claim42322 ∧
      (∀ x y z : NeutralNode,
        neutralIsLUB x y z ↔ neutralIsLUB y x z) ∧
      (∀ x z : NeutralNode,
        neutralIsLUB x x z ↔ z = x) ∧
      (∀ x y z a b c d : NeutralNode,
        neutralIsLUB x y a →
          neutralIsLUB a z b →
            neutralIsLUB y z c →
              neutralIsLUB x c d →
                b = d) ∧
      (∀ x y : NeutralNode, ∃! z, neutralIsLUB x y z)

end MathlibPlus.Open.ResearchFormalizationBatch01_01a000fa
