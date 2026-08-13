import Mathlib.Combinatorics.SimpleGraph.Maps

namespace MathlibPlus.GraphTheory

/-- Claim 43987: fixing one graph isomorphism from `G` to `H` identifies all such
isomorphisms with graph automorphisms of `G`. -/
def graphIsoEquivAut
    {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (base : G ≃g H) : (G ≃g H) ≃ (G ≃g G) where
  toFun iso := base.symm.comp iso
  invFun aut := base.comp aut
  left_inv iso := by
    apply RelIso.ext
    intro v
    simp [SimpleGraph.Iso.comp_assoc]
  right_inv aut := by
    apply RelIso.ext
    intro v
    simp [SimpleGraph.Iso.comp_assoc]

end MathlibPlus.GraphTheory
