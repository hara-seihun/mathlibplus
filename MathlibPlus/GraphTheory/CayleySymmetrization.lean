import Batteries
import Mathlib.Combinatorics.SimpleGraph.Cayley

namespace MathlibPlus.GraphTheory

open scoped Pointwise

/-- Adding all inverse generators does not change a simple multiplicative
Cayley graph: its edge relation has already forgotten orientation. -/
theorem mulCayley_symmetrization {G : Type*} [Group G] (S : Set G) :
    SimpleGraph.mulCayley (S ∪ S⁻¹) = SimpleGraph.mulCayley S := by
  rw [SimpleGraph.mulCayley_union, SimpleGraph.mulCayley_inv, sup_idem]

/-- The exact kernel of the directed-to-undirected Cayley construction:
two connection sets define the same simple Cayley graph iff their inversion
symmetrizations agree after deleting the identity. -/
theorem mulCayley_eq_iff_symmetrized_loopless_eq
    {G : Type*} [Group G] (S T : Set G) :
    SimpleGraph.mulCayley S = SimpleGraph.mulCayley T ↔
      (S ∪ S⁻¹) \ {1} = (T ∪ T⁻¹) \ {1} := by
  have hmem (U : Set G) (x : G) :
      x ∈ (U ∪ U⁻¹) \ {1} ↔ (SimpleGraph.mulCayley U).Adj 1 x := by
    simp [SimpleGraph.mulCayley_adj, Set.mem_sdiff, and_comm, ne_comm]
  constructor
  · intro h
    ext x
    rw [hmem, hmem, h]
  · intro h
    calc
      SimpleGraph.mulCayley S =
          SimpleGraph.mulCayley ((S ∪ S⁻¹) \ {1}) := by
            rw [SimpleGraph.mulCayley_erase_one, mulCayley_symmetrization]
      _ = SimpleGraph.mulCayley ((T ∪ T⁻¹) \ {1}) := by rw [h]
      _ = SimpleGraph.mulCayley T := by
            rw [SimpleGraph.mulCayley_erase_one, mulCayley_symmetrization]

/-- On inverse-closed identity-free connection sets, the simple Cayley-graph
constructor is faithful. -/
theorem mulCayley_eq_iff_of_inverseClosed_identityFree
    {G : Type*} [Group G] (S T : Set G)
    (hSinv : S = S⁻¹) (hTinv : T = T⁻¹)
    (hSone : 1 ∉ S) (hTone : 1 ∉ T) :
    SimpleGraph.mulCayley S = SimpleGraph.mulCayley T ↔ S = T := by
  rw [mulCayley_eq_iff_symmetrized_loopless_eq]
  simpa [← hSinv, ← hTinv, hSone, hTone]

/-- Equal inversion symmetrizations force equality of the underlying ordinary
undirected Cayley graphs. This is the precise information-loss mechanism by
which a directed defect may disappear after forgetting orientation. -/
theorem mulCayley_eq_of_symmetrization_eq
    {G : Type*} [Group G] {S T : Set G} (h : S ∪ S⁻¹ = T ∪ T⁻¹) :
    SimpleGraph.mulCayley S = SimpleGraph.mulCayley T :=
  (mulCayley_eq_iff_symmetrized_loopless_eq S T).2 (congrArg (· \ {1}) h)

end MathlibPlus.GraphTheory
