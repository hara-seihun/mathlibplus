import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace MathlibPlus.Combinatorics

/--
Claim 30664.  In a 72-element additive group, an inverse-closed connection
set of valency 15 has complementary valency 56 inside the nonidentity
 elements.  The exact group identification and Cayley-graph construction
remain explicit fidelity boundaries.
-/
theorem complementaryConnectionValency_claim30664
    {G : Type*} [Fintype G] [DecidableEq G] [AddGroup G]
    (S : Finset G) (hS : S.card = 15)
    (hInv : ∀ x, x ∈ S → -x ∈ S) (h0 : (0 : G) ∉ S)
    (hG : Fintype.card G = 72) :
    (Finset.univ \ ({0} ∪ S)).card = 56 := by
  have hdis : Disjoint ({0} : Finset G) S := by
    rw [Finset.disjoint_left]
    intro x hx0 hxS
    simp only [Finset.mem_singleton] at hx0
    exact h0 (hx0 ▸ hxS)
  have hcard : ({0} ∪ S).card = 16 := by
    rw [Finset.card_union_of_disjoint hdis]
    simp [hS]
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
  rw [Finset.card_univ, hcard, hG]

end MathlibPlus.Combinatorics
