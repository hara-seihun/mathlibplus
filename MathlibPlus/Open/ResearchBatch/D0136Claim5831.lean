import Mathlib

namespace MathlibPlus.Open.ResearchBatch.D0136Claim5831

/--
Extension of the restricted character.  For a finite elementary abelian
2-group `A` and a finite abelian odd-order group `B`, the character induced by
`b` on its linearity subgroup extends to `A × B`.
-/
def claim_5831
    (A B : Type*)
    [AddCommGroup A] [Fintype A]
    (hA : ∀ a : A, a + a = 0)
    [AddCommGroup B] [Fintype B]
    (hB : Odd (Fintype.card B))
    (b : A × B → ZMod 2)
    (hb0 : b 0 = 0) : Prop :=
  let L_b : Set (A × B) :=
    {x | ∀ u : A × B, b (x + u) = b x + b u}
  ∃ χ : (A × B) →+ ZMod 2,
    ∀ x ∈ L_b, χ x = b x

end MathlibPlus.Open.ResearchBatch.D0136Claim5831
