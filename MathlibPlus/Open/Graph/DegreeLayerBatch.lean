import Mathlib

namespace MathlibPlus.Open.Graph

private def armLength (α β γ : ℕ) (i : Fin 3) : ℕ :=
  if i = 0 then α else if i = 1 then β else γ

private abbrev SpiderArm (α β γ : ℕ) :=
  Σ i : Fin 3, Fin (armLength α β γ i)

private abbrev SpiderVertex (α β γ : ℕ) := Option (SpiderArm α β γ)

private def spiderAdj (α β γ : ℕ) : SpiderVertex α β γ → SpiderVertex α β γ → Prop
  | none, none => False
  | none, some ⟨i, k⟩ => k.val = 0
  | some ⟨i, k⟩, none => k.val = 0
  | some ⟨i, k⟩, some ⟨j, l⟩ =>
      i = j ∧ (k.val + 1 = l.val ∨ l.val + 1 = k.val)

private def generalizedSpider (α β γ : ℕ) : SimpleGraph (SpiderVertex α β γ) where
  Adj := spiderAdj α β γ
  symm := ⟨by
    intro u v h
    cases u <;> cases v <;> simp_all [spiderAdj, and_comm, or_comm]⟩
  loopless := ⟨by
    intro u
    cases u with
    | none => simp [spiderAdj]
    | some p =>
        rcases p with ⟨i, k⟩
        simp [spiderAdj]⟩

def threeArmGeneralizedSpiderIsTree (α β γ : ℕ) : Prop :=
  (generalizedSpider α β γ).IsTree

private abbrev CardVertex {V : Type*} (v : V) := {w : V // w ≠ v}

private def cardGraph {V : Type*} [DecidableEq V] (G : SimpleGraph V) (v : V) :
    SimpleGraph (CardVertex v) where
  Adj a b := G.Adj a.1 b.1
  symm := ⟨by
    intro a b h
    exact G.symm.symm a b h⟩
  loopless := ⟨by
    intro a h
    exact G.loopless.irrefl a.1 h⟩

private noncomputable def trueCardNeighborhood {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (v : V) : Finset (CardVertex v) := by
  classical
  exact Finset.univ.filter (fun w => G.Adj v w.1)

private noncomputable def cardDegree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (v : V) (w : CardVertex v) : ℕ := by
  classical
  exact (Finset.univ.filter (fun z => (cardGraph G v).Adj w z)).card

private noncomputable def sameDegreeLayerData {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (v : V) (X Y : Finset (CardVertex v)) : Prop :=
  Y.card = X.card ∧
    ∀ d : ℕ,
      (Y.filter (fun w => cardDegree G v w = d)).card =
        (X.filter (fun w => cardDegree G v w = d)).card

private def cardAutomorphismOrbit {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (v : V) (X Y : Finset (CardVertex v)) : Prop :=
  ∃ σ : Equiv (CardVertex v) (CardVertex v),
    (∀ a b, (cardGraph G v).Adj (σ a) (σ b) ↔ (cardGraph G v).Adj a b) ∧
      ∀ w, w ∈ Y ↔ σ w ∈ X

def degreeLayerRigid {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (v : V) : Prop :=
  ∀ Y : Finset (CardVertex v),
    sameDegreeLayerData G v (trueCardNeighborhood G v) Y →
      cardAutomorphismOrbit G v (trueCardNeighborhood G v) Y

private def sixVertexEdges : Finset (Finset (Fin 6)) :=
  {{0, 1}, {0, 3}, {0, 5}, {1, 2}, {1, 4}, {2, 3}}

private def sixVertexAdj (i j : Fin 6) : Prop :=
  ({i, j} : Finset (Fin 6)) ∈ sixVertexEdges

private def sixVertexGraph : SimpleGraph (Fin 6) where
  Adj := sixVertexAdj
  symm := ⟨by
    intro i j h
    simpa [sixVertexAdj, Finset.pair_comm] using h⟩
  loopless := ⟨by
    intro i h
    simp only [sixVertexAdj, sixVertexEdges, Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h | h | h | h | h | h <;>
      have hcard := congrArg Finset.card h <;> simp at hcard⟩

def explicitSixVertexGraphStatement : Prop :=
  ∃ G : SimpleGraph (Fin 6),
    ∀ i j, G.Adj i j ↔ sixVertexAdj i j

private def graphIsomorphic {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  ∃ e : Equiv V W, ∀ a b, G.Adj a b ↔ H.Adj (e a) (e b)

private def graphComplement {V : Type*} (G : SimpleGraph V) : SimpleGraph V where
  Adj a b := a ≠ b ∧ ¬ G.Adj a b
  symm := ⟨by
    intro a b h
    exact ⟨h.1.symm, fun hba => h.2 (G.symm.symm b a hba)⟩⟩
  loopless := ⟨by
    intro a h
    exact h.1 rfl⟩

private def hasNoDegreeLayerRigidCard {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : Prop :=
  ∀ v, ¬ degreeLayerRigid G v

def sixVertexDegreeLayerCensus : Prop :=
  ∃ G₁ G₂ G₃ G₄ : SimpleGraph (Fin 6),
    hasNoDegreeLayerRigidCard G₁ ∧
    hasNoDegreeLayerRigidCard G₂ ∧
    hasNoDegreeLayerRigidCard G₃ ∧
    hasNoDegreeLayerRigidCard G₄ ∧
    (graphIsomorphic sixVertexGraph G₁ ∨
      graphIsomorphic sixVertexGraph G₂ ∨
      graphIsomorphic sixVertexGraph G₃ ∨
      graphIsomorphic sixVertexGraph G₄) ∧
    (∀ G : SimpleGraph (Fin 6),
      hasNoDegreeLayerRigidCard G →
        graphIsomorphic G G₁ ∨ graphIsomorphic G G₂ ∨
          graphIsomorphic G G₃ ∨ graphIsomorphic G G₄) ∧
    (¬ graphIsomorphic G₁ G₂ ∧
      ¬ graphIsomorphic G₁ G₃ ∧
      ¬ graphIsomorphic G₁ G₄ ∧
      ¬ graphIsomorphic G₂ G₃ ∧
      ¬ graphIsomorphic G₂ G₄ ∧
      ¬ graphIsomorphic G₃ G₄) ∧
    graphIsomorphic (graphComplement G₁) G₂ ∧
    graphIsomorphic (graphComplement G₂) G₁ ∧
    graphIsomorphic (graphComplement G₃) G₄ ∧
    graphIsomorphic (graphComplement G₄) G₃ ∧
    (∀ n : ℕ, 0 < n → n < 6 →
      ∀ G : SimpleGraph (Fin n), ¬ hasNoDegreeLayerRigidCard G)

end MathlibPlus.Open.Graph
