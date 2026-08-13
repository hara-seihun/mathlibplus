import Batteries
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Combinatorics.SimpleGraph.Cayley

namespace MathlibPlus.GraphTheory

open scoped Pointwise

/-- A homomorphism carries inverse symmetrization to inverse symmetrization, but
passing to a loopless connection set deletes the whole source kernel, not merely
the source identity. -/
theorem image_symmetrized_sdiff_ker
    {G H : Type*} [Group G] [Group H] (f : G →* H) (S : Set G) :
    f '' ((S ∪ S⁻¹) \ (f.ker : Set G)) =
      (f '' S ∪ (f '' S)⁻¹) \ {1} := by
  change f '' ((S ∪ S⁻¹) \ f ⁻¹' {1}) = _
  rw [Set.image_sdiff_preimage, Set.image_union, Set.image_inv]

private theorem mulCayley_eq_iff_looplessSymmetrizations_eq
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
            rw [SimpleGraph.mulCayley_erase_one,
              SimpleGraph.mulCayley_union, SimpleGraph.mulCayley_inv, sup_idem]
      _ = SimpleGraph.mulCayley ((T ∪ T⁻¹) \ {1}) := by rw [h]
      _ = SimpleGraph.mulCayley T := by
            rw [SimpleGraph.mulCayley_erase_one,
              SimpleGraph.mulCayley_union, SimpleGraph.mulCayley_inv, sup_idem]

/-- Exact kernel-aware image formula for ordinary Cayley graphs. Two images
of directed connection sets define the same simple Cayley graph exactly when
the images of their inverse symmetrizations agree after all source elements
mapping to the identity have been deleted. -/
theorem mulCayley_image_eq_iff_symmetrized_sdiff_ker_image_eq
    {G H : Type*} [Group G] [Group H] (f : G →* H) (S T : Set G) :
    SimpleGraph.mulCayley (f '' S) = SimpleGraph.mulCayley (f '' T) ↔
      f '' ((S ∪ S⁻¹) \ (f.ker : Set G)) =
        f '' ((T ∪ T⁻¹) \ (f.ker : Set G)) := by
  rw [mulCayley_eq_iff_looplessSymmetrizations_eq,
    ← image_symmetrized_sdiff_ker, ← image_symmetrized_sdiff_ker]

end MathlibPlus.GraphTheory
