import MathlibPlus.Basic

universe u

namespace MathlibPlus.Combinatorics.Claim48698

/-- The connected-edge boundary polynomial of a finite unrooted tree, written
on the unordered edge type used by Mathlib's finite graph API. -/
def connectedEdgeBoundaryPolynomial
    {V : Type u} [Fintype V] [DecidableEq V] (T : SimpleGraph V)
    (_hT : T.IsTree) [DecidableRel T.Adj] (v : ℚ) : ℚ :=
  Finset.sum T.edgeFinset (fun e =>
    v ^ (Sym2.lift
      ⟨fun a b => T.degree a + T.degree b - 2, by
        intro a b
        simp [add_comm]
      ⟩ e))

end MathlibPlus.Combinatorics.Claim48698
