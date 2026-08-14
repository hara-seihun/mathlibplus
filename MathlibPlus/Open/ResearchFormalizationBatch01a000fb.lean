import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalizationBatch01a000fb

noncomputable section

abbrev State (m : ℕ) := Fin (m + 1)
abbrev Variable (m : ℕ) := Fin m ⊕ (Fin m ⊕ Unit)
abbrev Polynomial (m : ℕ) := MvPolynomial (Variable m) ℤ

/-- The variable used for the positive state `s`. -/
def xVar {m : ℕ} (s : Fin m) : Variable m := Sum.inl s

/-- The diagonal edge variable used for the positive state `s`. -/
def zVar {m : ℕ} (s : Fin m) : Variable m := Sum.inr (Sum.inl s)

def yVar {m : ℕ} : Variable m := Sum.inr (Sum.inr ())

def stateWeight (m : ℕ) (s : State m) : Polynomial m :=
  Fin.cases 1 (fun r => MvPolynomial.X (xVar r)) s

def edgeWeight (m : ℕ) (s t : State m) : Polynomial m :=
  if h : s = t then
    Fin.cases 1 (fun r => MvPolynomial.X (zVar r)) s
  else MvPolynomial.X yVar

def stateLambda (m : ℕ) (s : State m) : Polynomial m :=
  ∑ t : State m, edgeWeight m s t * stateWeight m t

def stateEdgeFactor {V : Type} (m : ℕ) (σ : V → State m) : Sym2 V → Polynomial m :=
  Sym2.lift
    ⟨fun v w => edgeWeight m (σ v) (σ w), by
      intro v w
      by_cases h : σ v = σ w
      · simp [edgeWeight, h]
      · have h' : ¬ σ w = σ v := by
          intro h'
          exact h h'.symm
        simp [edgeWeight, h, h']⟩

/-- The state-sum partition polynomial with the variables specified in the packet. -/
noncomputable def statePartitionPolynomial {V : Type} [Fintype V]
    (m : ℕ) (G : SimpleGraph V) : Polynomial m :=
  letI : Fintype G.edgeSet := Fintype.ofFinite G.edgeSet
  letI : Fintype (V → State m) := Fintype.ofFinite _
  ∑ σ : V → State m,
    (∏ v : V, stateWeight m (σ v)) *
      (∏ e ∈ G.edgeFinset, stateEdgeFactor m σ e)

def augmentGraph {V : Type} (G : SimpleGraph V) (v : V) (k : ℕ) :
    SimpleGraph (V ⊕ Fin k) :=
  SimpleGraph.fromRel (fun a b =>
    match a, b with
    | Sum.inl x, Sum.inl y => G.Adj x y
    | Sum.inl x, Sum.inr _ => x = v
    | Sum.inr _, Sum.inl y => y = v
    | Sum.inr _, Sum.inr _ => False)

def rootAugmentation {V : Type} [Fintype V]
    (m k : ℕ) (G : SimpleGraph V) : Polynomial m :=
  ∑ v : V, statePartitionPolynomial m (augmentGraph G v k)

def rootAugmentationFormula {V : Type} [Fintype V]
    (m k : ℕ) (G : SimpleGraph V) : Polynomial m :=
  (Fintype.card V : Polynomial m) * stateLambda m 0 ^ k +
    ∑ s : Fin m,
      (stateLambda m (Fin.succ s) ^ k - stateLambda m 0 ^ k) *
        (MvPolynomial.X (xVar s) *
          MvPolynomial.pderiv (xVar s) (statePartitionPolynomial m G))

/-- Claim 52094: all-root leaf augmentation is the stated differential image. -/
def claim52094 : Prop :=
  ∀ (m : ℕ), 1 ≤ m → ∀ {V : Type} [Fintype V]
    (T : SimpleGraph V), T.IsTree → ∀ k : ℕ,
      rootAugmentation m k T = rootAugmentationFormula m k T

/-- The path-edge factor in a spine load word. -/
def pathFactor (m ℓ : ℕ) (s : Fin ℓ → State m) (i : Fin (ℓ - 1)) :
    Polynomial m :=
  edgeWeight m
    (s ⟨i.1, by omega⟩)
    (s ⟨i.1 + 1, by omega⟩)

def transferPolynomial (d : Fin ℓ → ℕ) : Polynomial 2 :=
  ∑ s : Fin ℓ → State 2,
    (∏ i : Fin ℓ, stateWeight 2 (s i) * stateLambda 2 (s i) ^ d i) *
      (∏ i : Fin (ℓ - 1), pathFactor 2 ℓ s i)

def caterpillarPartitionPolynomial (m ℓ : ℕ) (d : Fin ℓ → ℕ) : Polynomial m :=
  ∑ s : Fin ℓ → State m,
    ∑ t : (i : Fin ℓ) × Fin (d i) → State m,
      (∏ i : Fin ℓ, stateWeight m (s i)) *
        (∏ a : (i : Fin ℓ) × Fin (d i), stateWeight m (t a)) *
        (∏ i : Fin (ℓ - 1), pathFactor m ℓ s i) *
        (∏ a : (i : Fin ℓ) × Fin (d i),
          edgeWeight m (s a.1) (t a))

/-- Claim 52085: the three-state load-word sum is the caterpillar partition polynomial. -/
def claim52085 : Prop :=
  ∀ (ℓ : ℕ) (d : Fin ℓ → ℕ),
    transferPolynomial d = caterpillarPartitionPolynomial 2 ℓ d

abbrev CaterpillarVertex (ℓ : ℕ) (d : Fin ℓ → ℕ) :=
  Fin ℓ ⊕ ((i : Fin ℓ) × Fin (d i))

def caterpillarGraph (d : Fin ℓ → ℕ) : SimpleGraph (CaterpillarVertex ℓ d) :=
  SimpleGraph.fromRel (fun a b =>
    match a, b with
    | Sum.inl i, Sum.inl j => i.1 + 1 = j.1 ∨ j.1 + 1 = i.1
    | Sum.inl i, Sum.inr leaf => i = leaf.1
    | Sum.inr leaf, Sum.inl i => leaf.1 = i
    | Sum.inr _, Sum.inr _ => False)

def graphIsomorphic {V W : Type} (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  ∃ e : V ≃ W, ∀ v w, G.Adj v w ↔ H.Adj (e v) (e w)

def wordA (i : Fin 6) : ℕ :=
  match i.1 with
  | 0 => 3
  | 1 => 3
  | 2 => 0
  | 3 => 1
  | 4 => 2
  | _ => 2

def wordB (i : Fin 6) : ℕ :=
  match i.1 with
  | 0 => 3
  | 1 => 0
  | 2 => 1
  | 3 => 2
  | 4 => 3
  | _ => 2

def coefficientWitness : Variable 2 →₀ ℕ :=
  Finsupp.single (xVar (1 : Fin 2)) 2 + Finsupp.single (yVar : Variable 2) 6

/-- Claim 52087: the displayed order-seventeen cyclic switch is nonisomorphic and has
    the displayed coefficient. -/
def claim52087 : Prop :=
  Fintype.card (CaterpillarVertex 6 wordA) = 17 ∧
  Fintype.card (CaterpillarVertex 6 wordB) = 17 ∧
  (caterpillarGraph wordA).IsTree ∧
  (caterpillarGraph wordB).IsTree ∧
  ¬ graphIsomorphic (caterpillarGraph wordA) (caterpillarGraph wordB) ∧
  MvPolynomial.coeff coefficientWitness
      (transferPolynomial wordA - transferPolynomial wordB) = 1

def rootMessage {V : Type} [Fintype V]
    (m : ℕ) (G : SimpleGraph V) (v : V) (s : State m) : Polynomial m :=
  letI : Fintype G.edgeSet := Fintype.ofFinite G.edgeSet
  letI : Fintype (V → State m) := Fintype.ofFinite _
  ∑ σ : V → State m,
    if σ v = s then
      (∏ x : V, stateWeight m (σ x)) *
        (∏ e ∈ G.edgeFinset, stateEdgeFactor m σ e)
    else 0

def rootMessageVector {V : Type} [Fintype V]
    (m : ℕ) (G : SimpleGraph V) (v : V) : State m → Polynomial m :=
  fun s => rootMessage m G v s

def aggregateRootMessage {V : Type} [Fintype V]
    (m : ℕ) (G : SimpleGraph V) : State m → Polynomial m :=
  fun s => ∑ v : V, rootMessage m G v s

def rootTraceTuple {V : Type} [Fintype V]
    (m : ℕ) (G : SimpleGraph V) (v : V) : Fin (m + 1) → Polynomial m :=
  fun k => statePartitionPolynomial m (augmentGraph G v k)

def rootFreeTrace {V : Type} [Fintype V]
    (m k : ℕ) (G : SimpleGraph V) : Polynomial m :=
  rootAugmentation m k G

def vandermondeMatrix (m : ℕ) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) (Polynomial m) :=
  fun k s => stateLambda m s ^ k.1

def traceAt (m k : ℕ) (a : State m → Polynomial m) : Polynomial m :=
  ∑ s : State m, stateLambda m s ^ k * a s

def vandermondeMap (m : ℕ)
    (a : State m → Polynomial m) : State m → Polynomial m :=
  fun k => traceAt m k.1 a

/-- Claim 52099: all-root traces recover the aggregate message vector through the
    Vandermonde transform. -/
def claim52099 : Prop :=
  ∀ (m : ℕ), 1 ≤ m → ∀ {V : Type} [Fintype V]
    (T : SimpleGraph V), T.IsTree →
    (∀ k : ℕ,
      rootFreeTrace m k T = traceAt m k (aggregateRootMessage m T)) ∧
    Matrix.det (vandermondeMatrix m) =
      ∏ s : State m, ∏ t ∈ Finset.univ.filter (fun t : State m => s < t),
        (stateLambda m t - stateLambda m s) ∧
    Matrix.det (vandermondeMatrix m) ≠ 0 ∧
    Function.Injective (vandermondeMap m)

/-- Claim 52103: the specified-root tuple and the root-free aggregate are distinct
    constructions, with the former recovering the rooted message vector. -/
def claim52103 : Prop :=
  ∀ (m : ℕ), 1 ≤ m → ∀ {V : Type} [Fintype V]
    (T : SimpleGraph V), T.IsTree → ∀ v : V,
      rootTraceTuple m T v = vandermondeMap m (rootMessageVector m T v) ∧
      Function.Injective (vandermondeMap m) ∧
      (∀ k : ℕ,
        rootFreeTrace m k T = traceAt m k (aggregateRootMessage m T))

def edgeGraph {n : ℕ} (E : Finset (Fin n × Fin n)) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel (fun v w => (v, w) ∈ E)

def edgesA : Finset (Fin 11 × Fin 11) :=
  {(0, 1), (0, 7), (1, 2), (1, 5), (1, 6), (2, 3), (2, 4), (7, 8), (7, 10), (8, 9)}

def edgesB : Finset (Fin 11 × Fin 11) :=
  {(0, 1), (0, 5), (0, 10), (1, 2), (2, 3), (2, 4), (5, 6), (5, 8), (5, 9), (6, 7)}

def treeA : SimpleGraph (Fin 11) := edgeGraph edgesA
def treeB : SimpleGraph (Fin 11) := edgeGraph edgesB

def rootMessageMultiset {V : Type} [Fintype V]
    (m : ℕ) (G : SimpleGraph V) : Multiset (State m → Polynomial m) :=
  (Finset.univ : Finset V).val.map (rootMessageVector m G)

/-- Claim 52106: the explicit order-eleven pair has equal one-state partition
    polynomial and all-root traces, but different root-message multisets. -/
def claim52106 : Prop :=
  (treeA).IsTree ∧
  (treeB).IsTree ∧
  ¬ graphIsomorphic treeA treeB ∧
  statePartitionPolynomial 1 treeA = statePartitionPolynomial 1 treeB ∧
  rootMessageMultiset 1 treeA ≠ rootMessageMultiset 1 treeB ∧
  ∀ k : ℕ, rootAugmentation 1 k treeA = rootAugmentation 1 k treeB

end

end MathlibPlus.Open.ResearchFormalizationBatch01a000fb
