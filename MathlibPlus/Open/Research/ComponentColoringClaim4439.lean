import MathlibPlus.Open.Research.BatchD0014

namespace MathlibPlus.Open.ResearchBatch.D0014

/-- A coloring of the two edge copies is constant on every connected component
of the equality graph. -/
def componentColoring_claim4439 {V C : Type*}
    (c : CardCocycle V)
    (left right : SimpleEdge V → C) : Prop :=
  ∀ x y, equalityComponent c x y →
    Sum.elim left right x = Sum.elim left right y

end MathlibPlus.Open.ResearchBatch.D0014
