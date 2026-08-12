import Mathlib.Data.Set.Card
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Operations

namespace MathlibPlus.Open.GraphTheory

/-- Claim 44118, expanded in Mathlib's finite-simple-graph model.  The source's
``(5,5)-good`` hypothesis is the absence of both a 5-clique and a 5-independent
set; the two `R(4,5,22)` conclusions are expanded in the same way. -/
def rootedGoodGraph_claim44118 : Prop :=
  ∀ (G : SimpleGraph (Fin 45)) (v : Fin 45),
    (∀ x, Set.ncard (G.neighborSet x) = 22) →
    let A : Set (Fin 45) := G.neighborSet v
    let B : Set (Fin 45) := Set.univ \ (insert v A)
    let P : SimpleGraph A := G.induce A
    let H : SimpleGraph B := (G.induce B)ᶜ
    ((∀ S : Finset (Fin 45), S.card = 5 →
        ¬ (∀ x ∈ S, ∀ y ∈ S, x ≠ y → G.Adj x y)) ∧
      (∀ S : Finset (Fin 45), S.card = 5 →
        ¬ (∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬G.Adj x y))) →
      Set.ncard A = 22 ∧
      Set.ncard B = 22 ∧
      (∀ S : Finset A, S.card = 4 →
        ¬ (∀ x ∈ S, ∀ y ∈ S, x ≠ y → P.Adj x y)) ∧
      (∀ S : Finset A, S.card = 5 →
        ¬ (∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬P.Adj x y)) ∧
      (∀ S : Finset B, S.card = 4 →
        ¬ (∀ x ∈ S, ∀ y ∈ S, x ≠ y → H.Adj x y)) ∧
      (∀ S : Finset B, S.card = 5 →
        ¬ (∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬H.Adj x y)) ∧
      Set.ncard P.edgeSet + Set.ncard H.edgeSet = 220 ∧
      (∀ a : A,
        Set.ncard (G.neighborSet (a : Fin 45) ∩ B) =
          21 - Set.ncard (P.neighborSet a)) ∧
      (∀ b : B,
        Set.ncard (G.neighborSet (b : Fin 45) ∩ A) =
          1 + Set.ncard (H.neighborSet b))

end MathlibPlus.Open.GraphTheory
