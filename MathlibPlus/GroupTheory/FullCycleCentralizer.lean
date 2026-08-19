import Mathlib

namespace MathlibPlus.GroupTheory

/-!
# Centralizer of a full cycle

Formalization of admitted claim 24812. A `p`-cycle on one size-`p` block is
represented by a permutation of `Fin p` that is an `IsCycle` and has full
support. Its generated subgroup is `Subgroup.zpowers c`.
-/

/-- Claim 24812: the centralizer in `S_p` of a full `p`-cycle is the cyclic
subgroup it generates. -/
def fullCycleCentralizer_eq_zpowers : Prop :=
  ∀ (p : ℕ) (c : Equiv.Perm (Fin p)),
    c.IsCycle → c.support = Finset.univ →
      Subgroup.centralizer ({c} : Set (Equiv.Perm (Fin p))) =
        Subgroup.zpowers c

end MathlibPlus.GroupTheory
