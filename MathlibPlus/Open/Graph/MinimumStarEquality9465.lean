import Mathlib

universe u

namespace MathlibPlus.Open.Graph

noncomputable section

/-- The set of undirected edges incident with a vertex. -/
def edgeStar {V : Type u} (Y : SimpleGraph V) (v : V) : Set (Sym2 V) :=
  {e | ∃ w, Y.Adj v w ∧ e = s(v, w)}

/-- The graph obtained by deleting a vertex and inducing on the remaining vertices. -/
def deletedGraph {V : Type u} (Y : SimpleGraph V) (v : V) : SimpleGraph {x : V // x ≠ v} :=
  Y.induce {x | x ≠ v}

/-- Finite degree, written directly so the finite carrier is explicit. -/
def vertexDegree {V : Type u} [Fintype V] (Y : SimpleGraph V) (v : V) : ℕ := by
  classical
  exact (Finset.univ.filter (fun w : V => Y.Adj v w)).card

def isMinimumDegree {V : Type u} [Fintype V] (Y : SimpleGraph V) (v : V) : Prop :=
  ∀ w : V, vertexDegree Y v ≤ vertexDegree Y w

/-- `{u,v}` is a connected component whose only edge is `u-v`. -/
def isK₂Component {V : Type u} (Y : SimpleGraph V) (u v : V) : Prop :=
  u ≠ v ∧ Y.Adj u v ∧
    ∀ w : V, w ≠ u → w ≠ v → ¬Y.Adj u w ∧ ¬Y.Adj v w

def hasNoIsolatedVertices {V : Type u} (Y : SimpleGraph V) : Prop :=
  ∀ x : V, ∃ y : V, Y.Adj x y

def isNotComplete {V : Type u} (Y : SimpleGraph V) : Prop :=
  Y ≠ SimpleGraph.completeGraph V

/--
The minimum layer of `Θ` is counted by distinct vertex stars (the convention
in the admitted minimum-layer statement).  For two vertices, this records
one occurrence exactly when their two star-indexed pairs coincide.
-/
def twoVertexThetaContribution {V : Type u} [Fintype V] (Y : SimpleGraph V)
    (u v : V) : Prop :=
  letI := Classical.decEq (Set (Sym2 V))
  ({edgeStar Y u, edgeStar Y v} : Finset (Set (Sym2 V))).card = 1

def claim9465 : Prop :=
  ∀ {V : Type u} [Fintype V] (Y : SimpleGraph V),
    hasNoIsolatedVertices Y → isNotComplete Y →
    ∀ u v : V,
      u ≠ v → isMinimumDegree Y u → isMinimumDegree Y v →
        (edgeStar Y u = edgeStar Y v ↔ isK₂Component Y u v) ∧
          (isK₂Component Y u v →
            Nonempty (deletedGraph Y u ≃g deletedGraph Y v) ∧
              twoVertexThetaContribution Y u v)

end
end MathlibPlus.Open.Graph
