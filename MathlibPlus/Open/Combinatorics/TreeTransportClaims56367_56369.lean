import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.TreeTransportClaims

/-- Occurrences retain the multiplicity of a vertex in an integral configuration. -/
def occurrence (V : Type*) (n : V → ℕ) := Σ v, Fin (n v)

instance occurrenceFintype {V : Type*} [Fintype V] (n : V → ℕ) :
    Fintype (occurrence V n) := by
  unfold occurrence
  infer_instance

/-- The cost of a matching of source occurrences to target occurrences. -/
def matchingCost {V : Type*} [Fintype V]
    (dist : V → V → ℕ) (e b : V → ℕ)
    (σ : occurrence V e ≃ occurrence V b) : ℕ :=
  ∑ o : occurrence V e, dist o.1 (σ o).1

def totalMass {V : Type*} [Fintype V] (n : V → ℕ) : ℕ :=
  ∑ v : V, n v

/-- The signed current across one selected side of a tree edge. -/
def cutCurrent {V : Type*} [DecidableEq V]
    (e b : V → ℕ) (S : Finset V) : ℤ :=
  S.sum (fun v => (e v : ℤ) - (b v : ℤ))

/-- The absolute current contribution of a selected edge side. -/
def cutCost {V : Type*} [DecidableEq V]
    (e b : V → ℕ) (edges : Finset (V × V))
    (side : V → V → Finset V) : ℕ :=
  edges.sum (fun uv => Int.natAbs (cutCurrent e b (side uv.1 uv.2)))

/-- No minimum matching crosses an edge backwards or crosses a zero-current edge. -/
def followsCurrent {V : Type*} [DecidableEq V]
    (e b : V → ℕ) (S : Finset V) (u v : V) : Prop :=
  let j := cutCurrent e b S
  (0 < j → ¬ (u ∉ S ∧ v ∈ S)) ∧
    (j < 0 → ¬ (u ∈ S ∧ v ∉ S)) ∧
    (j = 0 → (u ∈ S ↔ v ∈ S))

/-- An oriented representative list contains each undirected tree edge once. -/
def edgeRepresentatives {V : Type*} [DecidableEq V]
    (T : SimpleGraph V) (edges : Finset (V × V)) : Prop :=
  (∀ ⦃u v : V⦄, (u, v) ∈ edges → T.Adj u v) ∧
    (∀ ⦃u v : V⦄, T.Adj u v →
      ((u, v) ∈ edges ∨ (v, u) ∈ edges) ∧
      ¬ ((u, v) ∈ edges ∧ (v, u) ∈ edges))

/-- The selected side has exactly the represented tree edge as its boundary. -/
def edgeCutSides {V : Type*} [DecidableEq V]
    (T : SimpleGraph V) (edges : Finset (V × V))
    (side : V → V → Finset V) : Prop :=
  ∀ ⦃u v : V⦄, (u, v) ∈ edges →
    u ∈ side u v ∧ v ∉ side u v ∧
      ∀ ⦃x y : V⦄, T.Adj x y →
        (x ∈ side u v ↔ y ∉ side u v) →
        ((x, y) = (u, v) ∨ (x, y) = (v, u))

/-- The supplied distance is the length of the unique simple path in the finite tree. -/
def treeDistanceWitness {V : Type*}
    (T : SimpleGraph V) (hT : T.IsTree) (dist : V → V → ℕ) : Prop :=
  ∀ u v : V, ∃! p : T.Walk u v, p.IsPath ∧ p.length = dist u v

/-- A number is the minimum matching cost for the given occurrence multiset. -/
def minimumMatching {V : Type*} [Fintype V]
    (dist : V → V → ℕ) (e b : V → ℕ) (c : ℕ) : Prop :=
  (∃ σ : occurrence V e ≃ occurrence V b, matchingCost dist e b σ = c) ∧
    ∀ σ : occurrence V e ≃ occurrence V b, c ≤ matchingCost dist e b σ

/--
Tree-current characterization from Claim 56367.  The edge representatives and
cut sides are explicit finite-tree data, while `occurrence` makes repeated
configuration multiplicities part of the matching carrier.
-/
def treeCurrentCharacterization_claim56367 : Prop :=
  ∀ (V : Type*) [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (hT : T.IsTree)
    (edges : Finset (V × V)) (side : V → V → Finset V)
    (dist : V → V → ℕ) (e b : V → ℕ),
    edgeRepresentatives T edges →
    edgeCutSides T edges side →
    treeDistanceWitness T hT dist →
    totalMass e = totalMass b →
    ∃ c : ℕ,
      minimumMatching dist e b c ∧
      c = cutCost e b edges side ∧
      ∀ σ : occurrence V e ≃ occurrence V b,
        matchingCost dist e b σ = c →
        ∀ o : occurrence V e, ∀ u v : V, (u, v) ∈ edges →
          followsCurrent e b (side u v) o.1 (σ o).1

/-- A source-target pair occurs in at least one minimum matching. -/
def matchingSupportPair {V : Type*} [Fintype V]
    (dist : V → V → ℕ) (e b : V → ℕ) (c : ℕ)
    (u v : V) : Prop :=
  ∃ σ : occurrence V e ≃ occurrence V b,
    matchingCost dist e b σ = c ∧
      ∃ o : occurrence V e, o.1 = u ∧ (σ o).1 = v

/-- The bipartite support graph of all minimum matchings. -/
def matchingSupportGraph {V : Type*} [Fintype V]
    (dist : V → V → ℕ) (e b : V → ℕ) (c : ℕ) :
    SimpleGraph (V ⊕ V) where
  Adj a d :=
    (∃ u v : V, a = Sum.inl u ∧ d = Sum.inr v ∧
      matchingSupportPair dist e b c u v) ∨
    (∃ u v : V, a = Sum.inr v ∧ d = Sum.inl u ∧
      matchingSupportPair dist e b c u v)
  symm := by
    constructor
    intro a d h
    rcases h with h | h
    · rcases h with ⟨u, v, rfl, rfl, hp⟩
      exact Or.inr ⟨u, v, rfl, rfl, hp⟩
    · rcases h with ⟨u, v, rfl, rfl, hp⟩
      exact Or.inl ⟨u, v, rfl, rfl, hp⟩
  loopless := by
    constructor
    intro a h
    rcases h with h | h
    · rcases h with ⟨u, v, hau, hav, _⟩
      cases a <;> simp_all
    · rcases h with ⟨u, v, hav, hau, _⟩
      cases a <;> simp_all

/-- An induced cycle indexed by `ZMod n`; all nonconsecutive chords are excluded. -/
def inducedCycle {α : Type*} (G : SimpleGraph α) (n : ℕ) : Prop :=
  6 ≤ n ∧ Even n ∧
    ∃ c : ZMod n → α,
      Function.Injective c ∧
        ∀ i j : ZMod n,
          G.Adj (c i) (c j) ↔ i + 1 = j ∨ j + 1 = i

def noLongInducedEvenCycle {α : Type*} (G : SimpleGraph α) : Prop :=
  ∀ n : ℕ, ¬ inducedCycle G n

/-- A cost-neutral two-pair exchange around a support four-cycle. -/
def exchangeStep {V : Type*} [Fintype V]
    (dist : V → V → ℕ) (e b : V → ℕ) (c : ℕ)
    (σ τ : occurrence V e ≃ occurrence V b) : Prop :=
  ∃ a₁ a₂ : occurrence V e, ∃ d₁ d₂ : occurrence V b,
    a₁ ≠ a₂ ∧ d₁ ≠ d₂ ∧
    σ a₁ = d₁ ∧ σ a₂ = d₂ ∧
    τ a₁ = d₂ ∧ τ a₂ = d₁ ∧
    (∀ o : occurrence V e, o ≠ a₁ → o ≠ a₂ → τ o = σ o) ∧
    matchingSupportPair dist e b c a₁.1 d₁.1 ∧
    matchingSupportPair dist e b c a₁.1 d₂.1 ∧
    matchingSupportPair dist e b c a₂.1 d₁.1 ∧
    matchingSupportPair dist e b c a₂.1 d₂.1 ∧
    matchingCost dist e b σ = matchingCost dist e b τ

/--
Chordal-bipartite optimal-support theorem from Claim 56369, including its
four-cycle exchange consequence.  `noLongInducedEvenCycle` is the literal
induced-even-cycle definition of chordal-bipartite support.
-/
def chordalBipartiteOptimalSupport_claim56369 : Prop :=
  ∀ (V : Type*) [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (hT : T.IsTree)
    (dist : V → V → ℕ) (e b : V → ℕ) (c : ℕ),
    treeDistanceWitness T hT dist →
    totalMass e = totalMass b →
    minimumMatching dist e b c →
    noLongInducedEvenCycle (matchingSupportGraph dist e b c) ∧
      ∀ σ τ : occurrence V e ≃ occurrence V b,
        matchingCost dist e b σ = c →
        matchingCost dist e b τ = c →
        Relation.ReflTransGen (exchangeStep dist e b c) σ τ

end MathlibPlus.Open.TreeTransportClaims
