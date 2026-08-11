import Mathlib.Topology.Compactness.LocallyFinite

/-!
Formalization of admitted claim 11039.  “Quasi-compact” is represented by
`CompactSpace`, which is the separation-free compactness class in mathlib, and
“locally finite family” uses mathlib's `LocallyFinite` definition.
-/

namespace MathlibPlus.Topology.LocallyFinite

/-- A locally finite family of subsets of a quasi-compact space has only finitely
many nonempty members.  No separation axiom is used. -/
theorem finite_nonempty_of_compact_space
    {Y ι : Type*} [TopologicalSpace Y] [CompactSpace Y]
    {Z : ι → Set Y} (hZ : LocallyFinite Z) :
    {i | (Z i).Nonempty}.Finite := by
  exact hZ.finite_nonempty_of_compact

end MathlibPlus.Topology.LocallyFinite
