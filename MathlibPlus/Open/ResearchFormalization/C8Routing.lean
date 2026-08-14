import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.C8Routing

noncomputable section
open Classical

abbrev C8Vertex := Fin 8

def c8Adj (u v : C8Vertex) : Prop :=
  v.val = (u.val + 1) % 8 ∨ u.val = (v.val + 1) % 8

def c8BadEdge (u v : C8Vertex) : Prop :=
  (u = 0 ∧ v = 4) ∨ (u = 4 ∧ v = 0) ∨
  (u = 2 ∧ v = 6) ∨ (u = 6 ∧ v = 2)

def c8UnionAdj (u v : C8Vertex) : Prop := c8Adj u v ∨ c8BadEdge u v

def c8EvenSide : Finset C8Vertex :=
  Finset.univ.filter (fun v => v.val % 2 = 0)

def c8CutCount (adj : C8Vertex → C8Vertex → Prop)
    (S : Finset C8Vertex) : ℕ :=
  (Finset.univ.filter (fun e : C8Vertex × C8Vertex =>
    e.1.val < e.2.val ∧ adj e.1 e.2 ∧
      ((e.1 ∈ S) ≠ (e.2 ∈ S)))).card

def c8TriangleFree (adj : C8Vertex → C8Vertex → Prop) : Prop :=
  ∀ u v w : C8Vertex, u ≠ v → v ≠ w → u ≠ w →
    adj u v → adj v w → ¬ adj u w

def c8Connected : Prop :=
  ∀ u v : C8Vertex, Relation.ReflTransGen c8Adj u v

def c8Bipartite : Prop :=
  ∀ u v : C8Vertex, c8Adj u v → u.val % 2 ≠ v.val % 2

def c8CutDominant : Prop :=
  ∀ S : Finset C8Vertex,
    c8CutCount c8BadEdge S ≤ c8CutCount c8Adj S

def c8MaximumDisplayedCut : Prop :=
  ∀ S : Finset C8Vertex,
    c8CutCount c8UnionAdj S ≤ c8CutCount c8UnionAdj c8EvenSide

def c8WalkBetween (adj : C8Vertex → C8Vertex → Prop)
    (u v : C8Vertex) : List C8Vertex → Prop
  | [] => False
  | [x] => x = u ∧ x = v
  | x :: y :: rest => x = u ∧ adj x y ∧ c8WalkBetween adj y v (y :: rest)

def c8WalkOfLength (u v : C8Vertex) (n : ℕ) : Prop :=
  ∃ path : List C8Vertex,
    path.length = n + 1 ∧ c8WalkBetween c8Adj u v path

def c8DistanceFour (u v : C8Vertex) : Prop :=
  c8WalkOfLength u v 4 ∧ ∀ n < 4, ¬ c8WalkOfLength u v n

def c8UsesUndirectedEdge (u v : C8Vertex) : List C8Vertex → Prop
  | [] => False
  | [_] => False
  | x :: y :: rest =>
      (x = u ∧ y = v) ∨ (x = v ∧ y = u) ∨
        c8UsesUndirectedEdge u v (y :: rest)

def c8NoEdgeDisjointRouting : Prop :=
  ¬ ∃ path04 path26 : List C8Vertex,
    c8WalkBetween c8Adj 0 4 path04 ∧
    c8WalkBetween c8Adj 2 6 path26 ∧
    ∀ u v : C8Vertex,
      c8UsesUndirectedEdge u v path04 →
        ¬ c8UsesUndirectedEdge u v path26

/-- The concrete `C₈` instance with bad edges `04` and `26`. -/
def C8IntegralRoutingObstruction : Prop :=
  c8TriangleFree c8UnionAdj ∧
  c8Connected ∧
  c8Bipartite ∧
  c8CutDominant ∧
  c8DistanceFour 0 4 ∧
  c8DistanceFour 2 6 ∧
  c8MaximumDisplayedCut ∧
  c8NoEdgeDisjointRouting

end MathlibPlus.Open.ResearchFormalization.C8Routing
