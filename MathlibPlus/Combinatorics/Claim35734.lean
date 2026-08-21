-- UNVERIFIED (missing-import): submitted but not kernel-verified, so it is not built and MathlibPlus.lean does not import it. See unverified.txt.
import MathlibPlus.Combinatorics.Claim31610

open Set
open SimpleGraph

namespace MathlibPlus.Combinatorics.Claim35734

variable {A H : Type*} [Group A] [Group H] [Fintype A] [Fintype H]

/-- Adjacency in the complete-fiber Cayley graph is equality in the first
factor and inequality in the second. -/
theorem cayleyAdjacency (a a' : A) (h h' : H) :
    (mulCayley (({1} : Set A) ×ˢ ({1}ᶜ : Set H))).Adj (a, h) (a', h') ↔
      a = a' ∧ h ≠ h' := by
  exact MathlibPlus.Combinatorics.Claim31610.cayley_adjacency_iff a a' h h'

end MathlibPlus.Combinatorics.Claim35734
