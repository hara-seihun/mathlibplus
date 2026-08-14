import Mathlib

open scoped Classical BigOperators

namespace MathlibPlus.Open.GraphTheory.DeckInsertion

noncomputable section

/-- Finite simple graphs with Boolean adjacency make the labelled carrier
    finite while retaining symmetry and looplessness. -/
def FiniteSimpleGraph (V : Type*) [Fintype V] [DecidableEq V] :=
  {a : V → V → Bool //
    (∀ x y, a x y = a y x) ∧ (∀ x, a x x = false)}

def graphAdj {V : Type*} [Fintype V] [DecidableEq V]
    (G : FiniteSimpleGraph V) (x y : V) : Bool := G.1 x y

def graphIso {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    (G : FiniteSimpleGraph V) (H : FiniteSimpleGraph W) : Prop :=
  ∃ e : V ≃ W, ∀ x y, graphAdj G x y = graphAdj H (e x) (e y)

def deleteGraph {V : Type*} [Fintype V] [DecidableEq V]
    (G : FiniteSimpleGraph V) (v : V) :
    FiniteSimpleGraph {x : V // x ≠ v} :=
  ⟨fun x y => graphAdj G x.1 y.1,
    ⟨fun x y => G.2.1 x.1 y.1, fun x => G.2.2 x.1⟩⟩

def insertGraph {n : ℕ}
    (H : FiniteSimpleGraph (Fin n)) (S : Finset (Fin n)) :
    FiniteSimpleGraph (Option (Fin n)) :=
  ⟨fun x y =>
      match x, y with
      | some a, some b => graphAdj H a b
      | none, some b => decide (b ∈ S)
      | some a, none => decide (a ∈ S)
      | none, none => false,
    ⟨by
      intro x y
      cases x <;> cases y <;> simp [graphAdj, H.2.1]
      , by
      intro x
      cases x <;> simp [graphAdj, H.2.2]⟩⟩

def deletionMultiplicity {n : ℕ}
    (G : FiniteSimpleGraph (Fin (n + 1)))
    (H : FiniteSimpleGraph (Fin n)) : ℕ :=
  Nat.card {v : Fin (n + 1) // graphIso (deleteGraph G v) H}

def insertionMultiplicity {n : ℕ}
    (H : FiniteSimpleGraph (Fin n))
    (G : FiniteSimpleGraph (Fin (n + 1))) : ℕ :=
  Nat.card {S : Finset (Fin n) // graphIso (insertGraph H S) G}

/-- Claim 4993. -/
def claim4993 : Prop :=
  ∀ (n : ℕ) (G : FiniteSimpleGraph (Fin (n + 1)))
    (H : FiniteSimpleGraph (Fin n)),
    deletionMultiplicity G H =
      Nat.card {v : Fin (n + 1) // graphIso (deleteGraph G v) H} ∧
    insertionMultiplicity H G =
      Nat.card {S : Finset (Fin n) // graphIso (insertGraph H S) G}

end
end MathlibPlus.Open.GraphTheory.DeckInsertion
