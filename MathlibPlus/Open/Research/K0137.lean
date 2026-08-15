import Mathlib

namespace MathlibPlus.Open.Research.K0137

open Classical

 def oneVertexExtension {V : Type} (C : SimpleGraph V) (X : Set V) :
    SimpleGraph (Option V) :=
  SimpleGraph.fromRel (fun u v =>
    match u, v with
    | none, none => False
    | none, some y => y ∈ X
    | some x, none => x ∈ X
    | some x, some y => C.Adj x y)

def cardFixingAutomorphism {V : Type} (C : SimpleGraph V)
    (e : V ≃ V) : Prop :=
  ∀ x y, C.Adj (e x) (e y) ↔ C.Adj x y

def claim9075 {V : Type} [Fintype V] (G : SimpleGraph (Option V))
    (C : SimpleGraph V) (X : Set V) (k : ℕ) : Prop :=
  (∀ x y, G.Adj (some x) (some y) ↔ C.Adj x y) ∧
    (∀ x, G.Adj (none : Option V) (some x) ↔ x ∈ X) ∧
    k = X.ncard ∧ G = oneVertexExtension C X

def extensionIsomorphismFixingCard {V : Type} (C : SimpleGraph V)
    (X Y : Set V) : Prop :=
  ∃ e : Option V ≃ Option V,
    e none = none ∧
      ∀ u v,
        (oneVertexExtension C X).Adj u v ↔
          (oneVertexExtension C Y).Adj (e u) (e v)

def claim9082 {V : Type} (C : SimpleGraph V) (X Y : Set V) : Prop :=
  extensionIsomorphismFixingCard C X Y ↔
    ∃ e : V ≃ V, cardFixingAutomorphism C e ∧ e '' X = Y

end MathlibPlus.Open.Research.K0137
