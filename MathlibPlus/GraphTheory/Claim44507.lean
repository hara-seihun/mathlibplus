import Mathlib

namespace MathlibPlus.GraphTheory

/-- Precomposition by a graph isomorphism identifies the copies of its source and
target in any fixed host graph. -/
theorem copyEquivOfGraphIso_claim44507
    {α β γ : Type*} (source : SimpleGraph α) (target : SimpleGraph β)
    (host : SimpleGraph γ) (e : source ≃g target) :
    Nonempty (SimpleGraph.Copy source host ≃ SimpleGraph.Copy target host) := by
  let f : SimpleGraph.Copy source host ≃ SimpleGraph.Copy target host :=
    { toFun := fun g => g.comp e.symm.toCopy
      invFun := fun g => g.comp e.toCopy
      left_inv := by
        intro g
        ext v
        simp
      right_inv := by
        intro g
        ext v
        simp }
  exact ⟨f⟩

end MathlibPlus.GraphTheory
