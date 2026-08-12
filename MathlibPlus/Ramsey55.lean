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

/-- A finite simple graph with neither a five-clique nor a five-independent set. -/
def isGood55 {V : Type*} [Finite V] (G : SimpleGraph V) : Prop :=
  G.CliqueFree 5 ∧ G.IndepSetFree 5

/-- The independent-set formulation is equivalent to clique-freeness of the complement. -/
theorem isGood55_iff_compl_cliqueFree {V : Type*} [Finite V] (G : SimpleGraph V) :
    isGood55 G ↔ G.CliqueFree 5 ∧ Gᶜ.CliqueFree 5 := by
  simp [isGood55]

end MathlibPlus.Ramsey55
