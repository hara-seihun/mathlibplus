import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Frontier

/--
The admitted tight Hall-neighborhood rigidity claim: a nonnegative flow whose
selected rows send all their mass into a selected set of capacity-tight
columns saturates those columns, with no flow into them from the other rows.
-/
def booleanCharacterTightHallNeighborhoodRigidity
    (N P : Type*) [Fintype N] [Fintype P]
    (f : N × P → ℝ) (a : N → ℝ) (b : P → ℝ)
    (X : Finset N) (G : Finset P) : Prop :=
  (∀ i : N, ∀ j : P, 0 ≤ f (i, j)) ∧
      (∀ i ∈ X, G.sum (fun j => f (i, j)) = a i) ∧
      (∀ j ∈ G, (Finset.univ.sum (fun i => f (i, j))) ≤ b j) ∧
      (X.sum (fun i => a i) = G.sum (fun j => b j)) →
    (∀ j ∈ G, (Finset.univ.sum (fun i => f (i, j))) = b j) ∧
      (∀ i : N, i ∉ X → ∀ j : P, j ∈ G → f (i, j) = 0)

end MathlibPlus.Open.Frontier
