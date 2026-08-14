import Mathlib

open Filter

noncomputable section

namespace MathlibPlus.Open.ResearchBatch.PlanarUnitDistance

def euclideanDistance (p q : ℝ × ℝ) : ℝ :=
  Real.sqrt ((p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2)

def unitDistancePairs (P : Finset (ℝ × ℝ)) : ℕ := by
  classical
  exact ((P.product P).filter (fun pq =>
    pq.1 < pq.2 ∧ euclideanDistance pq.1 pq.2 = 1)).card

def planarN1oUpperBound : Prop :=
  ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ P : Finset (ℝ × ℝ),
    N ≤ P.card →
      (unitDistancePairs P : ℝ) ≤ Real.rpow (P.card : ℝ) (1 + η)

def claim_11953 : Prop :=
  ∃ ε : ℝ, 0 < ε ∧
    ∃ P : ℕ → Finset (ℝ × ℝ),
      Tendsto (fun j => (P j).card) atTop atTop ∧
        (∀ j : ℕ,
          Real.rpow ((P j).card : ℝ) (1 + ε) ≤ unitDistancePairs (P j)) ∧
        ¬ planarN1oUpperBound

end MathlibPlus.Open.ResearchBatch.PlanarUnitDistance
