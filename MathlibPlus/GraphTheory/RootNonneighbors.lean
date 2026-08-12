import Mathlib

namespace MathlibPlus.GraphTheory

/-- The 43-vertex degree-18 root has 24 non-neighbors (excluding the root). -/
theorem rootNonneighborCount_fin43
    (G : SimpleGraph (Fin 43)) (v : Fin 43)
    (hdeg : (G.neighborSet v).ncard = 18) :
    (Gᶜ.neighborSet v).ncard = 24 := by
  rw [G.neighborSet_compl]
  have hcomp : ((G.neighborSet v)ᶜ).ncard = 25 := by
    rw [Set.ncard_compl]
    simp [hdeg]
  have hv : v ∈ (G.neighborSet v)ᶜ := by
    simp [SimpleGraph.mem_neighborSet]
  rw [Set.ncard_sdiff_singleton_of_mem hv]
  rw [hcomp]

end MathlibPlus.GraphTheory
