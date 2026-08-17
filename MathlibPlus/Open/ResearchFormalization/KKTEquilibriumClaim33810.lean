import Mathlib
import MathlibPlus.Open.ResearchFormalizationBatch_01a001bb_b98e_7f3f_a02c_7ec8b381d120

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.KKTEquilibriumClaim33810

noncomputable section

open MathlibPlus.Open.ResearchFormalizationBatch_01a001bb_b98e_7f3f_a02c_7ec8b381d120

/-- Exact strict probability weights on the two active edge families. -/
def strictActiveWeights {m : ℕ}
    (x : Fin m → planarVector)
    (α β : (Fin m × Fin m) → ℝ) : Prop :=
  (∀ p, p ∈ planarClosestPairs x → α p = 1 / (m : ℝ)) ∧
    (∀ p, p ∉ planarClosestPairs x → α p = 0) ∧
    (∀ p, p ∈ planarFarthestPairs x → β p = 1 / (m : ℝ)) ∧
    (∀ p, p ∉ planarFarthestPairs x → β p = 0) ∧
    (∀ p, p ∈ planarClosestPairs x → 0 < α p) ∧
    (∀ p, p ∈ planarFarthestPairs x → 0 < β p) ∧
    (∑ p ∈ planarClosestPairs x, α p) = 1 ∧
    (∑ p ∈ planarFarthestPairs x, β p) = 1

/-- The direct vertex equilibrium/KKT equation. -/
def kktEquilibrium {m : ℕ}
    (x : Fin m → planarVector)
    (α β : (Fin m × Fin m) → ℝ) : Prop :=
  ∀ w : Fin m → planarVector,
    (∑ p ∈ planarClosestPairs x,
      α p * planarVelocityValue x w p) =
      ∑ p ∈ planarFarthestPairs x,
        β p * planarVelocityValue x w p

/-- Claim 33810: the two active cycles carry the exact positive uniform
probability weights and satisfy the full closest--farthest KKT equilibrium. -/
def claim33810 : Prop :=
  ∀ (m : ℕ), 7 ≤ m → Odd m →
    let k := (m - 1) / 2
    let x := regularPolygon m
    (∀ p : Fin m × Fin m,
      p ∈ planarPairs m →
      (planarPairQ x p = 1 ↔ sideRelation p.1 p.2)) ∧
    (∀ p : Fin m × Fin m,
      p ∈ planarPairs m →
      (planarPairQ x p = planarPairMax x ↔
        farthestRelation k p.1 p.2)) ∧
    ∃ α β : (Fin m × Fin m) → ℝ,
      strictActiveWeights x α β ∧ kktEquilibrium x α β

end
end MathlibPlus.Open.ResearchFormalization.KKTEquilibriumClaim33810
