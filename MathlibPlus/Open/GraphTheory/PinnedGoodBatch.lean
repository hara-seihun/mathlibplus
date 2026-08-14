import Mathlib

namespace MathlibPlus.Open.GraphTheory.PinnedGood

/-- The `(5,5)`-good property used here is the simultaneous absence of a
five-clique and an independent five-set. -/
def IsGood55 {V : Type*} (G : SimpleGraph V) : Prop :=
  G.CliqueFree 5 ∧ G.IndepSetFree 5

/-- Claim 9137.  The indexed family is kept as an explicit injective
enumeration, rather than collapsing the witnesses to a cardinality claim. -/
def claim9137 : Prop :=
  ∃ W : Fin 328 → SimpleGraph (Fin 42),
    Function.Injective W ∧ ∀ i, IsGood55 (W i)

end MathlibPlus.Open.GraphTheory.PinnedGood
