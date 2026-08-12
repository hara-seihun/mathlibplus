import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic.NormNum

namespace MathlibPlus.Combinatorics.DiamondOrbit

/-- All subsets of the labeled vertex set, represented as a finite subtype. -/
def VertexSubset :=
  {s : Finset (Fin 4) // s ∈ (Finset.univ : Finset (Fin 4)).powerset}

instance : DecidableEq VertexSubset := by
  unfold VertexSubset
  infer_instance

noncomputable instance : Fintype VertexSubset := by
  unfold VertexSubset
  exact Finset.Subtype.fintype _

/-- The six possible labeled edges of `K₄`. -/
def EdgePair := {s : VertexSubset // s.1.card = 2}

instance : DecidableEq EdgePair := by
  unfold EdgePair
  infer_instance

noncomputable instance : Fintype EdgePair := Subtype.fintype _

/-- The action of a vertex permutation on the labeled two-subset edge type. -/
def permEdge (σ : Equiv.Perm (Fin 4)) (e : EdgePair) : EdgePair :=
  ⟨⟨e.1.1.image σ, by
      apply Finset.mem_powerset.mpr
      intro v hv
      rcases Finset.mem_image.mp hv with ⟨u, hu, rfl⟩
      exact Finset.mem_univ _⟩,
    by
      calc
        (e.1.1.image σ).card = e.1.1.card :=
          Finset.card_image_of_injective e.1.1 σ.injective
        _ = 2 := e.2⟩

theorem permEdge_inv_left (σ : Equiv.Perm (Fin 4)) (e : EdgePair) :
    permEdge σ⁻¹ (permEdge σ e) = e := by
  apply Subtype.ext
  apply Subtype.ext
  simp [permEdge, Finset.image_image]

theorem permEdge_inv_right (σ : Equiv.Perm (Fin 4)) (e : EdgePair) :
    permEdge σ (permEdge σ⁻¹ e) = e := by
  apply Subtype.ext
  apply Subtype.ext
  simp [permEdge, Finset.image_image]

/-- One fixed labeling of `K₄-e`; the missing edge is `{0,1}`. -/
def baseMissing : EdgePair :=
  ⟨⟨{0, 1}, by
      apply Finset.mem_powerset.mpr
      intro v hv
      simp at hv
      rcases hv with rfl | rfl <;> simp⟩, by decide⟩

/-- The actual labeled diamond graph, represented by its present edges. -/
noncomputable def diamondGraph : Finset EdgePair :=
  (Finset.univ : Finset EdgePair).erase baseMissing

/-- The induced action of a vertex permutation on an edge-set graph. -/
noncomputable def permGraph (σ : Equiv.Perm (Fin 4)) (G : Finset EdgePair) :
    Finset EdgePair :=
  G.image (permEdge σ)

/-- The genuine `S₄` orbit of the fixed labeled diamond under vertex
permutations. -/
noncomputable def s4Orbit : Finset (Finset EdgePair) :=
  (Finset.univ : Finset (Equiv.Perm (Fin 4))).image
    (fun σ => permGraph σ diamondGraph)

/-- The missing-edge-indexed family used to identify the orbit. -/
noncomputable def missingEdgeOrbit : Finset (Finset EdgePair) :=
  (Finset.univ : Finset EdgePair).image
    (fun missing => (Finset.univ : Finset EdgePair).erase missing)

theorem edgePair_card : Fintype.card EdgePair = 6 := by
  decide

theorem s4Orbit_eq_missingEdgeOrbit : s4Orbit = missingEdgeOrbit := by
  decide

theorem s4Orbit_card : s4Orbit.card = 6 := by
  decide

end MathlibPlus.Combinatorics.DiamondOrbit
