import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch

open scoped Classical

/-- The unrooted leaves of a finite simple graph. -/
noncomputable def leafVertices {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : Finset V :=
  Finset.univ.filter (fun x => G.degree x = 1)

/-- Vertices with no children after rooting a nontrivial tree at `root`. -/
noncomputable def rootedChildlessVertices {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (root : V) : Finset V :=
  Finset.univ.filter (fun x => x ≠ root ∧ G.degree x = 1)

noncomputable def rootedChildlessCount {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (root : V) : ℕ :=
  (rootedChildlessVertices G root).card

/-- Exact childless-root count and the resulting comparison of two rootings. -/
def rootedUnrootedTreeChildlessCount : Prop :=
  ∀ {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (v w : V),
    G.IsTree → 2 ≤ Fintype.card V →
      rootedChildlessVertices G v = (leafVertices G).erase v ∧
      rootedChildlessCount G v =
        (leafVertices G).card - (if G.degree v = 1 then 1 else 0) ∧
      (rootedChildlessCount G v ≠ rootedChildlessCount G w ↔
        ((G.degree v = 1 ∧ G.degree w ≠ 1) ∨
          (G.degree v ≠ 1 ∧ G.degree w = 1)))

end MathlibPlus.Open.ResearchFormalizationBatch
