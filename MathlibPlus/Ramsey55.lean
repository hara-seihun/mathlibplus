import Mathlib

/-!
# Elementary finite-graph counts for Ramsey (5,5)

A kernel-checked handshaking consequence extracted from Record 3 of legacy packet
`C-0228`.
-/

namespace MathlibPlus.Ramsey55

/-- An 18-regular simple graph on 43 vertices has exactly 387 edges. -/
theorem regular18_order43_edgeCount
    (G : SimpleGraph (Fin 43)) [DecidableRel G.Adj]
    (hreg : ∀ v, G.degree v = 18) :
    G.edgeFinset.card = 387 := by
  classical
  have hsum := G.sum_degrees_eq_twice_card_edges
  simp_rw [hreg] at hsum
  norm_num at hsum ⊢
  omega

end MathlibPlus.Ramsey55
