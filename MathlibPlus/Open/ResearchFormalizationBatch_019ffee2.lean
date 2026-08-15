import Mathlib

<<<<<<< ours
noncomputable section

namespace MathlibPlus.Open

open Polynomial

private def qTrace : Polynomial ℤ :=
  X ^ 7 - 8 * X ^ 5 + 19 * X ^ 3 - 12 * X + 1

private def qComplex : Polynomial ℂ :=
  qTrace.map (algebraMap ℤ ℂ)

/-- Claim 42105: Q is irreducible over the integers (and rationals), with all
seven complex roots real. -/
def claim_42105 : Prop :=
  Irreducible qTrace ∧
    Irreducible (qTrace.map (algebraMap ℤ ℚ)) ∧
    qComplex.natDegree = 7 ∧
    ∀ z : ℂ, IsRoot qComplex z → z.im = 0

/-- Claim 42106: exactly one root of Q is outside [-2,2], and the remaining
six roots are in that interval. -/
def claim_42106 : Prop :=
  qComplex.natDegree = 7 ∧
    qComplex.roots.card = 7 ∧
    (qComplex.roots.filter
      (fun z => z.im = 0 ∧ (z.re < -2 ∨ 2 < z.re))).card = 1 ∧
    (qComplex.roots.filter
      (fun z => z.im = 0 ∧ -2 ≤ z.re ∧ z.re ≤ 2)).card = 6 ∧
    ∀ z ∈ qComplex.roots, z.im = 0

private def rootsInTraceInterval (p : Polynomial ℤ) : Prop :=
  ∀ z : ℂ, IsRoot (p.map (algebraMap ℤ ℂ)) z →
    z.im = 0 ∧ -2 ≤ z.re ∧ z.re ≤ 2

/-- Claim 42112: Q has no integer symmetric characteristic-polynomial
complement whose roots all lie in [-2,2]. -/
def claim_42112 : Prop :=
  ¬ ∃ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℤ) (C : Polynomial ℤ),
    M.IsSymm ∧ rootsInTraceInterval C ∧ Matrix.charpoly M = qTrace * C

private noncomputable def treeAdjacencyMatrix (n : ℕ)
    (G : SimpleGraph (Fin n)) : Matrix (Fin n) (Fin n) ℤ := by
  classical
  exact G.adjMatrix ℤ

private def treeCharpoly (n : ℕ) (G : SimpleGraph (Fin n)) : Polynomial ℚ :=
  (Matrix.charpoly (treeAdjacencyMatrix n G)).map (algebraMap ℤ ℚ)

private def totallyRealAlgebraicInteger (α : ℂ) : Prop :=
  IsIntegral ℤ α ∧ IsAlgebraic ℚ α ∧
    ∀ z : ℂ,
      IsRoot ((minpoly ℚ α).map (algebraMap ℚ ℂ)) z → z.im = 0

private def treeRoot (n : ℕ) (G : SimpleGraph (Fin n)) (α : ℂ) : Prop :=
  IsRoot ((treeCharpoly n G).map (algebraMap ℚ ℂ)) α

/-- Claim 42110: every totally real algebraic integer is a finite-tree
adjacency eigenvalue, equivalently its minimal polynomial divides a finite-tree
characteristic polynomial. -/
def claim_42110 : Prop :=
  ∀ α : ℂ, totallyRealAlgebraicInteger α →
    (∃ (n : ℕ) (G : SimpleGraph (Fin n)),
      G.IsTree ∧ treeRoot n G α) ∧
    (∃ (n : ℕ) (G : SimpleGraph (Fin n)),
      G.IsTree ∧ minpoly ℚ α ∣ treeCharpoly n G)

/-- Claim 41266: the arithmetic consequence of the two displayed identities
in the leaf-rooted comparison. -/
def claim_41266 : Prop :=
  ∀ a b c d : ℕ,
    2 ≤ a ∧ 2 ≤ b ∧ 2 ≤ c ∧ 2 ≤ d →
    a * (a - 1) * b * (b - 1) = c * (c - 1) * d * (d - 1) →
    (a : ℚ) + b - 6 / a = (c : ℚ) + d - 6 / c →
    a > c →
      ((d : ℚ) - b = ((a - c : ℕ) : ℚ) * (a * c + 6) / (a * c) ∧
        a * c ∣ 6 * (a - c) ∧
        c < 6 ∧
        a ∣ 6 * c ∧
        ((a, c) = (3, 2) ∨ (a, c) = (6, 2) ∨ (a, c) = (6, 3) ∨
          (a, c) = (12, 4) ∨ (a, c) = (30, 5)))

/-- Claim 42123: sufficiently high 3-power cyclotomic roots do not lie in a
fixed finite extension of the 3-adic field. -/
def claim_42123 : Prop :=
  ∀ (K : Type) [Field K] [Algebra ℚ_[3] K]
    [FiniteDimensional ℚ_[3] K],
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      ∀ z : K,
        ¬ IsRoot ((cyclotomic (3 ^ k) ℤ).map (algebraMap ℤ K)) z

end MathlibPlus.Open
=======
namespace MathlibPlus.Open.ResearchFormalizationBatch_019ffee2

noncomputable section
open Classical

variable {V : Type} [Fintype V] [DecidableEq V]

def orderedEdgeCount (G : SimpleGraph V) : ℕ :=
  ((Finset.univ : Finset (V × V)).filter (fun p : V × V => G.Adj p.1 p.2)).card / 2

def triangleFree (G : SimpleGraph V) : Prop :=
  ∀ ⦃u v w : V⦄, G.Adj u v → G.Adj v w → G.Adj w u → False

def crossingAdj (G : SimpleGraph V) (S : Finset V) (u v : V) : Prop :=
  G.Adj u v ∧ ((u ∈ S ∧ v ∉ S) ∨ (u ∉ S ∧ v ∈ S))

def crossingGraph (G : SimpleGraph V) (S : Finset V) : SimpleGraph V :=
  SimpleGraph.fromRel (crossingAdj G S)

def internalAdj (G : SimpleGraph V) (S : Finset V) (u v : V) : Prop :=
  G.Adj u v ∧ ((u ∈ S ∧ v ∈ S) ∨ (u ∉ S ∧ v ∉ S))

def bipartizationDefect (G : SimpleGraph V) (S : Finset V) : ℕ :=
  ((Finset.univ : Finset (V × V)).filter (fun p : V × V => internalAdj G S p.1 p.2)).card / 2

def isMaximumCut (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ T : Finset V,
    orderedEdgeCount (crossingGraph G T) ≤ orderedEdgeCount (crossingGraph G S)

def claim46797 : Prop :=
  ∀ (N : ℕ) (G : SimpleGraph (Fin N)) (S : Finset (Fin N)),
    triangleFree G →
    isMaximumCut G S →
    (SimpleGraph.IsAcyclic (crossingGraph G S)) →
    bipartizationDefect G S ≤ N ^ 2 / 25 ∧
      (bipartizationDefect G S = N ^ 2 / 25 →
        Nonempty (SimpleGraph.Iso G (SimpleGraph.cycleGraph 5)))

def layersPartition {d : ℕ} (L : Fin (d + 1) → Finset V) : Prop :=
  ∀ v, ∃! i, v ∈ L i

def consecutiveLayerPair {d : ℕ} (L : Fin (d + 1) → Finset V) (u v : V) : Prop :=
  ∃ i : Fin d,
    (u ∈ L i.castSucc ∧ v ∈ L i.succ) ∨
      (u ∈ L i.succ ∧ v ∈ L i.castSucc)

def endpointLayer {d : ℕ} : Fin (d + 1) :=
  ⟨d, Nat.lt_succ_self d⟩

def endpointInternalPair {d : ℕ} (L : Fin (d + 1) → Finset V) (u v : V) : Prop :=
  (u ∈ L 0 ∧ v ∈ L endpointLayer) ∨
    (u ∈ L endpointLayer ∧ v ∈ L 0)

def oneLayeredBlockPresentation {d : ℕ} (G : SimpleGraph V) (S : Finset V)
    (L : Fin (d + 1) → Finset V) : Prop :=
  isMaximumCut G S ∧
    (∀ i, (L i).Nonempty) ∧
    layersPartition L ∧
    (∀ ⦃u v⦄, crossingAdj G S u v → consecutiveLayerPair L u v) ∧
    (∀ ⦃u v⦄, internalAdj G S u v → endpointInternalPair L u v)

def completeBetween {d : ℕ} (G : SimpleGraph V) (L : Fin (d + 1) → Finset V)
    (i j : Fin (d + 1)) : Prop :=
  ∀ ⦃u v : V⦄, u ∈ L i → v ∈ L j → G.Adj u v

def equalLayerSizes {d : ℕ} (L : Fin (d + 1) → Finset V) : Prop :=
  ∀ i j, (L i).card = (L j).card

def balancedC5Blowup (G : SimpleGraph V) : Prop :=
  ∃ (L : Fin 5 → Finset V),
    (∀ i, (L i).Nonempty) ∧
    layersPartition L ∧
    equalLayerSizes L ∧
    (∀ ⦃u v : V⦄,
      G.Adj u v ↔
        (∃ i : Fin 5,
          (u ∈ L i ∧ v ∈ L ⟨(i.1 + 1) % 5, Nat.mod_lt _ (by decide)⟩) ∨
            (u ∈ L ⟨(i.1 + 1) % 5, Nat.mod_lt _ (by decide)⟩ ∧ v ∈ L i)))

def claim46799 : Prop :=
  ∀ (N d : ℕ) (G : SimpleGraph (Fin N)) (S : Finset (Fin N))
    (L : Fin (d + 1) → Finset (Fin N)),
    triangleFree G →
    oneLayeredBlockPresentation G S L →
    bipartizationDefect G S ≤ N ^ 2 / 25 ∧
      (bipartizationDefect G S = N ^ 2 / 25 ↔
        (d = 4 ∧ equalLayerSizes L ∧
          (∀ i : Fin d, completeBetween G L i.castSucc i.succ) ∧
          completeBetween G L 0 endpointLayer)) ∧
      (bipartizationDefect G S = N ^ 2 / 25 → balancedC5Blowup G)

def pathGraph5 : SimpleGraph (Fin 5) :=
  SimpleGraph.fromRel (fun u v : Fin 5 => u.1 + 1 = v.1 ∨ v.1 + 1 = u.1)

def nextIndex {k : ℕ} (hk : 0 < k) (i : Fin k) : Fin k :=
  ⟨(i.1 + 1) % k, Nat.mod_lt _ hk⟩

def simpleCycle (H : SimpleGraph V) (k : ℕ) (f : Fin k → V) : Prop :=
  ∃ h : 3 ≤ k, Function.Injective f ∧
    ∀ i : Fin k,
      H.Adj (f i)
        (f (nextIndex (lt_of_lt_of_le (by decide : 0 < 3) h) i))

def isConnected (H : SimpleGraph V) : Prop :=
  ∀ u v, u = v ∨ Relation.TransGen H.Adj u v

def cycleEdgeSet {k : ℕ} (f : Fin k → V) (hk : 0 < k) : Finset (V × V) :=
  (Finset.univ.image (fun i : Fin k => (f i, f (nextIndex hk i)))) ∪
    (Finset.univ.image (fun i : Fin k => (f (nextIndex hk i), f i)))

def isCactus (H : SimpleGraph V) : Prop :=
  ∀ (k l : ℕ) (f : Fin k → V) (g : Fin l → V) (hk : 0 < k) (hl : 0 < l),
    simpleCycle H k f →
    simpleCycle H l g →
    cycleEdgeSet f hk = cycleEdgeSet g hl ∨
      ((Finset.univ.image f) ∩ (Finset.univ.image g)).card ≤ 1

def claim46831 : Prop :=
  (∀ (n : ℕ) (G : SimpleGraph (Fin (5 * n))) (S : Finset (Fin (5 * n))),
    triangleFree G →
    isMaximumCut G S →
    isConnected (crossingGraph G S) →
    isCactus (crossingGraph G S) →
    (bipartizationDefect G S = n ^ 2 ∧ n ^ 2 = (5 * n) ^ 2 / 25) →
    n = 1 ∧ Nonempty (SimpleGraph.Iso G (SimpleGraph.cycleGraph 5))) ∧
  (∃ S : Finset (Fin 5),
    isMaximumCut (SimpleGraph.cycleGraph 5) S ∧
    bipartizationDefect (SimpleGraph.cycleGraph 5) S = 1 ∧
    1 = 5 ^ 2 / 25 ∧
    Nonempty (SimpleGraph.Iso
      (crossingGraph (SimpleGraph.cycleGraph 5) S) pathGraph5) ∧
    isConnected (crossingGraph (SimpleGraph.cycleGraph 5) S) ∧
    isCactus (crossingGraph (SimpleGraph.cycleGraph 5) S))

end

end MathlibPlus.Open.ResearchFormalizationBatch_019ffee2
>>>>>>> theirs
