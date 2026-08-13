import Mathlib

namespace MathlibPlus.Algebra.Claim58744

/--
Arithmetic core of claim 58744: once the all-gap decomposition supplies
`wtG - wtM = n - 2*d`, the strict half-order condition forces a positive
weight gap. The multiset equality `wt P = wt Q` remains a source-level
hypothesis outside this scalar consequence.
-/
theorem positiveWeightGap (n d wtG wtM : ℤ)
    (hhalf : 2 * d < n)
    (hgap : wtG - wtM = n - 2 * d) :
    0 < wtG - wtM := by
  linarith

end MathlibPlus.Algebra.Claim58744

namespace MathlibPlus.Algebra.Claim58669

/--
Arithmetic core of claim 58669: a path image whose order is the child order
`d - 1` plus at least one path step has order at least the host order `d`.
The source-specific meanings of child products and `N` are recorded in the
alignment boundary rather than silently introduced here.
-/
theorem pathImageOrderAtLeastHost (d m tailOrder : ℕ)
    (hd : 1 ≤ d)
    (hm : 1 ≤ m)
    (htail : tailOrder = d - 1 + m) :
    d ≤ tailOrder := by
  omega

end MathlibPlus.Algebra.Claim58669
