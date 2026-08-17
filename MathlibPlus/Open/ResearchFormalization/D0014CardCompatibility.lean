import MathlibPlus.Open.Research.BatchD0014

namespace MathlibPlus.Open.ResearchBatch.D0014

/-- Claim 4440: compatibility of two edge colorings with every prescribed
card map at every deleted vertex avoided by the edge. -/
def cardCompatibility_claim4440 {V C : Type*}
    (c : CardCocycle V) (left right : SimpleEdge V → C) : Prop :=
  ∀ (i : V) (e : SimpleEdge V), avoids i e →
    left e = right (cardMap c i e)

end MathlibPlus.Open.ResearchBatch.D0014
