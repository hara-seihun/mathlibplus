import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Data.Fintype.BigOperators
import Mathlib.SetTheory.Cardinal.Finite

namespace MathlibPlus.GraphTheory.ComponentCopyTuple

/-- Claim 44481: the tuple of one labelled copy for each finite component
index has the dependent-product cardinality.  The host and component-pattern
semantics are intentionally represented by the explicit family `Copy`; the
claim does not specify a more concrete graph encoding. -/
theorem card_pi_copy
    {I H : Type*} [Fintype I] [Fintype H]
    (Copy : I → H → Type*) (h : H)
    [∀ i : I, Fintype (Copy i h)] :
    Nat.card (∀ i : I, Copy i h) =
      ∏ i : I, Nat.card (Copy i h) := by
  classical
  exact Nat.card_pi

end MathlibPlus.GraphTheory.ComponentCopyTuple
