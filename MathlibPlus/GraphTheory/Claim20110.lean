import Mathlib
import Mathlib.Tactic

namespace MathlibPlus.GraphTheory.Claim20110

/--
Claim 20110.  The edge sets of `H`, `C`, and `T` are represented explicitly;
`C` and `T` have the tree edge counts for orders `n - 1` and `n`.  The
positivity premise makes the displayed natural-number subtraction coincide
with the intended edge-count arithmetic.
-/
theorem edgeRedundancy_formula
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]
    (eH eC eT : Finset E) (vC vT : Finset V) (n : ℕ)
    (hn : 2 ≤ n)
    (hTreeC : eC.card = vC.card - 1)
    (hTreeT : eT.card = vT.card - 1)
    (hOrderC : vC.card = n - 1)
    (hOrderT : vT.card = n) :
    eH.card + eC.card - eT.card = eH.card - 1 := by
  omega

end MathlibPlus.GraphTheory.Claim20110
