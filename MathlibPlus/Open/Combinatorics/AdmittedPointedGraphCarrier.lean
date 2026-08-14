import Mathlib

noncomputable section

namespace MathlibPlus.Open.ResearchFormalizationBatch

structure PointedFiniteSimpleGraph where
  n : ℕ
  graph : SimpleGraph (Fin n)
  root : Fin n

def PointedGraphIso (G H : PointedFiniteSimpleGraph) : Prop :=
  ∃ e : Fin G.n ≃ Fin H.n,
    e G.root = H.root ∧
      ∀ u v, G.graph.Adj u v ↔ H.graph.Adj (e u) (e v)

abbrev pointedGraphSpace (I : Type) := I →₀ ℚ

/-- Claim 22972: the free rational space on finite pointed graph isomorphism classes. -/
def claim22972 : Prop :=
  ∃ (I : Type) (representative : I → PointedFiniteSimpleGraph),
    (∀ G : PointedFiniteSimpleGraph, ∃ i, PointedGraphIso (representative i) G) ∧
    (∀ i j, i = j ↔ PointedGraphIso (representative i) (representative j)) ∧
    Nonempty (Module.Basis I ℚ (pointedGraphSpace I))

end MathlibPlus.Open.ResearchFormalizationBatch
