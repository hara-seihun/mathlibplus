import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch

/-- The four edges of the cyclic four-vertex block orbit. -/
def c4Edges_13271 : Fin 4 → Fin 4 × Fin 4 :=
  ![(0, 1), (1, 2), (2, 3), (3, 0)]

/-- Every vertex occurs in two of the four cyclic edge blocks. -/
def c4ReplicationNumber_13271 (v : Fin 4) : ℕ :=
  (Finset.univ.filter (fun e : Fin 4 =>
    v = (c4Edges_13271 e).1 ∨ v = (c4Edges_13271 e).2)).card

/-- The exact inverse-paired cyclic vertex log-modulus ledger. -/
def c4VertexLogModuli_13271 (a b : ℝ) : Fin 4 → ℝ :=
  ![a, b, -b, -a]

/-- The exact inverse-paired cyclic edge-weight ledger. -/
def c4EdgeWeights_13271 (a b : ℝ) : Fin 4 → ℝ :=
  ![a + b, 0, -(a + b), 0]

/--
The overlapping four-cycle has replication number two, but for positive `a` and
`b` its exact edge ledger has one positive, two zero, and one negative entry.
Thus overlap alone supplies no second positive block.
-/
def overlapDoesNotForceSecondPositiveBlock_13271 : Prop :=
  (∀ v : Fin 4, c4ReplicationNumber_13271 v = 2) ∧
    ∀ a b : ℝ, 0 < a → 0 < b →
      let v := c4VertexLogModuli_13271 a b
      let w := c4EdgeWeights_13271 a b
      (v 0 = a ∧ v 1 = b ∧ v 2 = -b ∧ v 3 = -a ∧
          v 0 = -v 3 ∧ v 1 = -v 2 ∧ (∑ i, v i) = 0) ∧
        (0 < w 0 ∧ w 1 = 0 ∧ w 2 < 0 ∧ w 3 = 0) ∧
        (Finset.card (Finset.univ.filter (fun i : Fin 4 => 0 < w i)) = 1) ∧
        ¬ ∃ i j : Fin 4, i ≠ j ∧ 0 < w i ∧ 0 < w j

end MathlibPlus.Open.ResearchFormalizationBatch
