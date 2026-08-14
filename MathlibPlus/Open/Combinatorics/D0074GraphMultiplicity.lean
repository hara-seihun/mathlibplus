import Mathlib

namespace MathlibPlus.Open.Combinatorics.D0074

noncomputable section

/-- Graph isomorphisms between finite simple graphs, with the carrier made
explicit instead of referring to an unspecified set of graph classes. -/
def finiteGraphIso {V W : Type*}
    (G : SimpleGraph V) (H : SimpleGraph W) : Type _ :=
  {e : V ≃ W // ∀ x y, G.Adj x y ↔ H.Adj (e x) (e y)}

def finiteGraphAut {V : Type*} (G : SimpleGraph V) : Type _ :=
  finiteGraphIso G G

def deletedGraph {n : ℕ}
    (G : SimpleGraph (Fin (n + 1))) (v : Fin (n + 1)) :
    SimpleGraph {x : Fin (n + 1) // x ≠ v} :=
  G.induce {x : Fin (n + 1) | x ≠ v}

/-- Adjoin one new vertex, whose neighborhood is the selected finite set. -/
def adjoinVertex {n : ℕ}
    (H : SimpleGraph (Fin n)) (S : Finset (Fin n)) :
    SimpleGraph (Option (Fin n)) :=
  SimpleGraph.fromRel (fun a b =>
    match a, b with
    | some x, some y => H.Adj x y
    | none, some y => y ∈ S
    | some x, none => x ∈ S
    | none, none => False)

def deletionMultiplicity {n : ℕ}
    (G : SimpleGraph (Fin (n + 1))) (H : SimpleGraph (Fin n)) : ℕ :=
  Nat.card {v : Fin (n + 1) //
    Nonempty (finiteGraphIso (deletedGraph G v) H)}

def insertionMultiplicity {n : ℕ}
    (H : SimpleGraph (Fin n)) (G : SimpleGraph (Fin (n + 1))) : ℕ :=
  Nat.card {S : Finset (Fin n) //
    Nonempty (finiteGraphIso (adjoinVertex H S) G)}

/-- Automorphism-weighted deletion/insertion multiplicity identity. -/
def claim4995 : Prop :=
  ∀ (n : ℕ) (H : SimpleGraph (Fin n))
    (G : SimpleGraph (Fin (n + 1))),
    insertionMultiplicity H G * Nat.card (finiteGraphAut G) =
      deletionMultiplicity G H * Nat.card (finiteGraphAut H)

end
end MathlibPlus.Open.Combinatorics.D0074
