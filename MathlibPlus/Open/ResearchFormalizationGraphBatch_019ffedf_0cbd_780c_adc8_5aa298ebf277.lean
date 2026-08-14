import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationGraphBatch

noncomputable section

open scoped BigOperators

/-- A simple cycle whose vertices all lie in a prescribed finite set. -/
def ContainsCycleOn {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : Prop :=
  ∃ k : ℕ, 3 ≤ k ∧
    ∃ v : ZMod k → Fin n,
      Function.Injective v ∧
        (∀ i, v i ∈ S) ∧
          (∀ i, G.Adj (v i) (v (i + 1)))

/-- Every five vertices induce a subgraph containing a cycle. -/
def IsCyclicFive {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  5 ≤ n ∧ ∀ S : Finset (Fin n), S.card = 5 → ContainsCycleOn G S

/-- The number of edges, counted once by orienting each edge increasingly. -/
def edgeCount {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ := by
  classical
  exact ((Finset.univ.product Finset.univ).filter
    (fun p => p.1 < p.2 ∧ G.Adj p.1 p.2)).card

/-- The degree, counted by filtering the finite vertex type. -/
def vertexDegree {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) : ℕ := by
  classical
  exact (Finset.univ.filter (fun w => G.Adj v w)).card

/-- The graph consisting of cliques on the two consecutive vertex blocks. -/
def cliqueUnion (a b : ℕ) : SimpleGraph (Fin (a + b)) :=
  SimpleGraph.fromRel (fun u v =>
    (u.1 < a ∧ v.1 < a) ∨ (a ≤ u.1 ∧ a ≤ v.1))

/-- The same union with the single bridge between vertices 0 and a. -/
def cliqueUnionWithBridge (a b : ℕ) : SimpleGraph (Fin (a + b)) :=
  SimpleGraph.fromRel (fun u v =>
    ((u.1 < a ∧ v.1 < a) ∨ (a ≤ u.1 ∧ a ≤ v.1)) ∨
      ((u.1 = 0 ∧ v.1 = a) ∨ (u.1 = a ∧ v.1 = 0)))

/-- The complete bipartite graph between the two blocks. -/
def completeBipartite (a b : ℕ) : SimpleGraph (Fin (a + b)) :=
  SimpleGraph.fromRel (fun u v =>
    (u.1 < a ∧ a ≤ v.1) ∨ (a ≤ u.1 ∧ v.1 < a))

/-- The complete bipartite graph between the two blocks, with one edge deleted. -/
def completeBipartiteMinusEdge (a b : ℕ) : SimpleGraph (Fin (a + b)) :=
  SimpleGraph.fromRel (fun u v =>
    ((u.1 < a ∧ a ≤ v.1) ∨ (a ≤ u.1 ∧ v.1 < a)) ∧
      ¬ ((u.1 = 0 ∧ v.1 = a) ∨ (u.1 = a ∧ v.1 = 0)))

/-- A graph is triangle-free when it has no three-vertex clique. -/
def IsTriangleFree {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ¬ ∃ T : Finset (Fin n), T.card = 3 ∧ G.IsClique (T : Set (Fin n))

/-- Independence number at most two, expressed by triangle-freeness of the complement. -/
def IndependenceNumberAtMostTwo {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  IsTriangleFree Gᶜ

/-- Order 10 one-edge-above classification. -/
def claim26163 : Prop :=
  ∀ H : SimpleGraph (Fin 10),
    IsCyclicFive H →
      edgeCount H = 21 →
        Nonempty (H ≃g cliqueUnion 4 6) ∨
          Nonempty (H ≃g cliqueUnionWithBridge 5 5)

/-- Order 11 one-edge-above classification. -/
def claim26164 : Prop :=
  ∀ H : SimpleGraph (Fin 11),
    IsCyclicFive H →
      edgeCount H = 26 →
        Nonempty (H ≃g cliqueUnionWithBridge 5 6)

/-- The order 10 slack function in the degree-slack inequality. -/
def Delta10 (d : ℕ) : ℚ :=
  if d = 0 then 7 / 25
  else 2 * ((d : ℚ) - 4) ^ 2 / (25 * ((d : ℚ) + 1))

/-- The order 11 slack function in the degree-slack inequality. -/
def Delta11 (d : ℕ) : ℚ :=
  if d = 0 then 1 / 3
  else ((d : ℚ) - 4) * ((d : ℚ) - 5) / (15 * ((d : ℚ) + 1))

/-- Degree multisets allowed by the order 10 slack and degree-sum constraints. -/
def order10AllowedDegreeMultisets : Set (Multiset (Fin 10)) :=
  {d |
    d.card = 10 ∧
      (d.map (fun x => (x : ℕ))).sum = 42 ∧
        (d.map (fun x => Delta10 (x : ℕ))).sum ≤ (4 : ℚ) / 25}

/-- Degree multisets allowed by the order 11 slack and degree-sum constraints. -/
def order11AllowedDegreeMultisets : Set (Multiset (Fin 11)) :=
  {d |
    d.card = 11 ∧
      (d.map (fun x => (x : ℕ))).sum = 52 ∧
        (d.map (fun x => Delta11 (x : ℕ))).sum ≤ (2 : ℚ) / 15}

/-- Order 10 degree-slack inequality and its exact finite census. -/
def claim26165 : Prop :=
  ∀ G : SimpleGraph (Fin 10),
    IsCyclicFive G →
      edgeCount G = 21 →
        (∑ v : Fin 10, Delta10 (vertexDegree G v)) ≤ (4 : ℚ) / 25 ∧
          (∑ v : Fin 10, vertexDegree G v) = 42 ∧
            Set.ncard order10AllowedDegreeMultisets = 13

/-- Order 11 degree-slack inequality and its exact finite census. -/
def claim26166 : Prop :=
  ∀ G : SimpleGraph (Fin 11),
    IsCyclicFive G →
      edgeCount G = 26 →
        (∑ v : Fin 11, Delta11 (vertexDegree G v)) ≤ (2 : ℚ) / 15 ∧
          (∑ v : Fin 11, vertexDegree G v) = 52 ∧
            Set.ncard order11AllowedDegreeMultisets = 29

/-- The neighborhood trace on an independent triple. -/
def neighborhoodTrace {n : ℕ} (G : SimpleGraph (Fin n))
    (T : Finset (Fin n)) (u : Fin n) : Set (Fin n) :=
  G.neighborSet u ∩ (T : Set (Fin n))

/-- Independent-triple trace constraints, including the square and triangle closures. -/
def IndependentTripleTraceConstraints {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ T : Finset (Fin n),
    T.card = 3 →
      Gᶜ.IsClique (T : Set (Fin n)) →
        (∀ u : Fin n, u ∉ T → (neighborhoodTrace G T u).Nonempty) ∧
          (∀ u v : Fin n,
            u ∉ T → v ∉ T → u ≠ v →
              let I := neighborhoodTrace G T u ∩ neighborhoodTrace G T v
              I.Nonempty ∧
                (2 ≤ Set.ncard I →
                  ∃ a b : Fin n,
                    a ∈ I ∧ b ∈ I ∧ a ≠ b ∧
                      G.Adj u a ∧ G.Adj a v ∧ G.Adj v b ∧ G.Adj b u) ∧
                (Set.ncard I = 1 →
                  G.Adj u v ∧ ∃ w : Fin n, w ∈ I))

/-- Independent-triple neighborhood constraints in a cyclic-five graph. -/
def claim26167 : Prop :=
  ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
    IsCyclicFive G → IndependentTripleTraceConstraints G

/-- Independence-number bound at the two boundary orders. -/
def claim26170 : Prop :=
  (∀ G : SimpleGraph (Fin 10),
      IsCyclicFive G → edgeCount G = 21 → IndependenceNumberAtMostTwo G) ∧
    (∀ G : SimpleGraph (Fin 11),
      IsCyclicFive G → edgeCount G = 26 → IndependenceNumberAtMostTwo G)

/-- Order 10 deficit-one Mantel classification, including the deletion form. -/
def deletedVertexGraph {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) :
    SimpleGraph {w : Fin n // w ≠ v} :=
  SimpleGraph.induce {w : Fin n | w ≠ v} G

def IsMinimumDegreeVertex {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) : Prop :=
  ∀ w : Fin n, vertexDegree G v ≤ vertexDegree G w

def claim26171 : Prop :=
  ∀ J : SimpleGraph (Fin 10),
    IsTriangleFree J →
      edgeCount J = 24 →
        (Nonempty (J ≃g completeBipartite 4 6) ∨
            Nonempty (J ≃g completeBipartiteMinusEdge 5 5)) ∧
          (∀ v : Fin 10,
            IsMinimumDegreeVertex J v →
              vertexDegree J v = 4 ∧
                Nonempty (deletedVertexGraph J v ≃g completeBipartite 4 5))

/-- Order 11 deficit-one Mantel classification, including its order-10 deletion. -/
def claim26172 : Prop :=
  ∀ J : SimpleGraph (Fin 11),
    IsTriangleFree J →
      edgeCount J = 29 →
        Nonempty (J ≃g completeBipartiteMinusEdge 5 6)

/-- The old vertex embedded in the ten-vertex pendant-pair completion. -/
def oldIndex (u : Fin 10) : Fin 8 :=
  ⟨u.1 % 8, Nat.mod_lt _ (by decide)⟩

/-- The unrooted graph obtained by attaching two new leaves at a root. -/
def pendantPairCompletion (D : SimpleGraph (Fin 8)) (x : Fin 8) :
    SimpleGraph (Fin 10) :=
  SimpleGraph.fromRel (fun u v =>
    (u.1 < 8 ∧ v.1 < 8 ∧ D.Adj (oldIndex u) (oldIndex v)) ∨
      ((u.1 = 8 ∧ v.1 = x.1) ∨ (u.1 = 9 ∧ v.1 = x.1)))

/-- The two distinguished new edges in the pendant-pair completion. -/
def pendantPairWedge (D : SimpleGraph (Fin 8)) (x : Fin 8) :
    Finset (Sym2 (Fin 10)) :=
  {Sym2.mk (⟨x.1, by omega⟩ : Fin 10) 8,
    Sym2.mk (⟨x.1, by omega⟩ : Fin 10) 9}

end
end MathlibPlus.Open.ResearchFormalizationGraphBatch
