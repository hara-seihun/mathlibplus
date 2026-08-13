import Mathlib

namespace MathlibPlus.GraphTheory

/-- The edge image induced by a map on the vertices of a finite edge. -/
def edgeImage {α : Type*} [DecidableEq α] (f : α → α)
    (e : Finset α) : Finset α := e.image f

/-- Claim 59192, in its exact nonempty-intersection form.  The point-fixing
hypothesis is retained although the symmetry argument only uses involutivity. -/
theorem involutiveIncidenceSymmetric_claim59192
    {G ι : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (f : G → G) (_hzero : f 0 = 0) (hinv : Function.Involutive f)
    (atomEdges : ι → Finset (Finset G)) (i j : ι) :
    (∃ e ∈ atomEdges i, ({edgeImage f e} ∩ atomEdges j).Nonempty) ↔
      (∃ e ∈ atomEdges j, ({edgeImage f e} ∩ atomEdges i).Nonempty) := by
  have hdouble (e : Finset G) : edgeImage f (edgeImage f e) = e := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
      rcases Finset.mem_image.mp hy with ⟨z, hz, rfl⟩
      simpa [hinv z] using hz
    · intro hx
      refine Finset.mem_image.mpr ⟨f x, ?_, hinv x⟩
      exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  constructor
  · rintro ⟨e, hei, ⟨z, hz⟩⟩
    have hz_parts := Finset.mem_inter.mp hz
    have hz_image : z = edgeImage f e := Finset.mem_singleton.mp hz_parts.1
    refine ⟨z, hz_parts.2, ⟨e, Finset.mem_inter.mpr ⟨?_, hei⟩⟩⟩
    exact Finset.mem_singleton.mpr (by rw [hz_image, hdouble])
  · rintro ⟨e, hej, ⟨z, hz⟩⟩
    have hz_parts := Finset.mem_inter.mp hz
    have hz_image : z = edgeImage f e := Finset.mem_singleton.mp hz_parts.1
    refine ⟨z, hz_parts.2, ⟨e, Finset.mem_inter.mpr ⟨?_, hej⟩⟩⟩
    exact Finset.mem_singleton.mpr (by rw [hz_image, hdouble])

end MathlibPlus.GraphTheory

namespace MathlibPlus.GraphTheory.Claim59196

abbrev G5 := (ZMod 5) × (ZMod 5)

def inversePairAtom (d : G5) : Finset G5 := {d, -d}

def swapInvolution : G5 ≃+ G5 :=
  { toFun := fun p => (p.2, p.1)
    invFun := fun p => (p.2, p.1)
    left_inv := by intro p; cases p; rfl
    right_inv := by intro p; cases p; rfl
    map_add' := by intro p q; cases p; cases q; rfl }

/-- The coordinate swap sends the two displayed inverse-pair atoms to one
another.  The atoms themselves remain distinct. -/
theorem swap_exchanges_distinct_atoms_claim59196 :
    (inversePairAtom ((1, 0) : G5)).image (swapInvolution : G5 → G5) =
        inversePairAtom ((0, 1) : G5) ∧
      inversePairAtom ((1, 0) : G5) ≠ inversePairAtom ((0, 1) : G5) := by
  constructor
  · ext x
    simp [inversePairAtom, swapInvolution]
  · intro h
    have hmem : ((1, 0) : G5) ∈ inversePairAtom ((0, 1) : G5) := by
      rw [← h]
      simp [inversePairAtom]
    simp [inversePairAtom] at hmem
    have hne : (1 : ZMod 5) ≠ 0 := by decide
    rcases hmem with ⟨h, _⟩ | h
    · exact hne h
    · exact hne h

end MathlibPlus.GraphTheory.Claim59196
