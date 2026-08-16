import Mathlib

namespace MathlibPlus.Open.GroupTheory

/-- Claim 40942 (source record `R-1322`).  The prose holomorph is represented by
`Subgroup.normalizer` in the full symmetric group; regularity is expressed by
unique transitivity of the subgroup subtype, and cyclicity/order are retained
as explicit predicates.  The semidirect-product isomorphism is not made an
additional hypothesis because the packet supplies no particular encoding of
that semidirect product. -/
def squarefreeHolomorphUniqueRegularCycle_claim40942 : Prop :=
  ∀ (m : ℕ), Squarefree m →
    ∀ (C : Subgroup (Equiv.Perm (Fin m))),
      IsCyclic C →
      Nat.card C = m →
      (∀ x y : Fin m, ∃! h : C, (h : Equiv.Perm (Fin m)) x = y) →
      ∀ (D : Subgroup (Equiv.Perm (Fin m))),
        D ≤ Subgroup.normalizer (C : Set (Equiv.Perm (Fin m))) →
        IsCyclic D →
        Nat.card D = m →
        (∀ x y : Fin m, ∃! h : D, (h : Equiv.Perm (Fin m)) x = y) →
        D = C

end MathlibPlus.Open.GroupTheory
