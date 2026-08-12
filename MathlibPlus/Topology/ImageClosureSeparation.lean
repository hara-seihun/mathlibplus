import Mathlib.Topology.Closure

open Set Filter
open scoped Topology

namespace MathlibPlus.Topology.ImageClosureSeparation

/-- Claim 56320: separating a point from the image of the bad set by an open
neighborhood is equivalent to avoiding its closure. -/
theorem image_closure_separation_iff
    {X Y : Type*} [TopologicalSpace Y]
    (S G : Set X) (D : X → Y) (x₀ : X) (_hx₀ : x₀ ∈ S) :
    (∃ U : Set Y, IsOpen U ∧ D x₀ ∈ U ∧ S ∩ D ⁻¹' U ⊆ G) ↔
      D x₀ ∉ closure (D '' (S \ G)) := by
  constructor
  · rintro ⟨U, hU, hU₀, hsub⟩ hcl
    rcases mem_closure_iff.1 hcl U hU hU₀ with ⟨y, hyU, hy⟩
    rcases hy with ⟨x, hx, rfl⟩
    exact hx.2 (hsub ⟨hx.1, hyU⟩)
  · intro hcl
    have hopen : IsOpen ((closure (D '' (S \ G)))ᶜ) :=
      isOpen_compl_iff.2 isClosed_closure
    refine ⟨(closure (D '' (S \ G)))ᶜ, hopen, ?_, ?_⟩
    · exact hcl
    · intro x hx
      by_contra hxG
      exact hx.2 (subset_closure ⟨x, ⟨hx.1, hxG⟩, rfl⟩)

end MathlibPlus.Topology.ImageClosureSeparation
