import Mathlib
import MathlibPlus.Open.ResearchFormalizationBatch_01a001bb_b98e_7f3f_a02c_7ec8b381d120

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.StressFeasibilityObstructionClaim33825

noncomputable section

open MathlibPlus.Open.ResearchFormalizationBatch_01a001bb_b98e_7f3f_a02c_7ec8b381d120

/-- The exact step-cycle Laplacian used in the signed stress. -/
def stepLaplacian (m s : ℕ) : Matrix (Fin m) (Fin m) ℝ :=
  fun i j =>
    if i = j then 2
    else if Nat.ModEq m (i.val + s) j.val ∨
      Nat.ModEq m (j.val + s) i.val then -1
    else 0

def signedStress (m k : ℕ) (D : ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  fun i j =>
    (1 / (m : ℝ)) *
      (stepLaplacian m 1 i j - (1 / D ^ 2) * stepLaplacian m k i j)

/-- No three vertices form a unit equilateral triangle. -/
def hasUnitTriangle {m : ℕ} (x : Fin m → planarVector) : Prop :=
  ∃ i j l : Fin m,
    i ≠ j ∧ i ≠ l ∧ j ≠ l ∧
      planarPairQ x (i, j) = 1 ∧
      planarPairQ x (i, l) = 1 ∧
      planarPairQ x (j, l) = 1

/-- Exact positive closest/farthest weights and their direct KKT equation. -/
def strictKKT {m : ℕ} (x : Fin m → planarVector) : Prop :=
  ∃ α β : (Fin m × Fin m) → ℝ,
    (∀ p, p ∈ planarClosestPairs x → α p = 1 / (m : ℝ)) ∧
    (∀ p, p ∉ planarClosestPairs x → α p = 0) ∧
    (∀ p, p ∈ planarFarthestPairs x → β p = 1 / (m : ℝ)) ∧
    (∀ p, p ∉ planarFarthestPairs x → β p = 0) ∧
    (∀ p, p ∈ planarClosestPairs x → 0 < α p) ∧
    (∀ p, p ∈ planarFarthestPairs x → 0 < β p) ∧
    (∑ p ∈ planarClosestPairs x, α p) = 1 ∧
    (∑ p ∈ planarFarthestPairs x, β p) = 1 ∧
    (∀ w : Fin m → planarVector,
      (∑ p ∈ planarClosestPairs x,
        α p * planarVelocityValue x w p) =
        ∑ p ∈ planarFarthestPairs x,
          β p * planarVelocityValue x w p)

/-- The complete stress-feasibility predicate, with no detached matrix. -/
def stressFeasible (m : ℕ) : Prop :=
  let k := (m - 1) / 2
  let x := regularPolygon m
  let D := planarDiameter x
  strictKKT x ∧
    Matrix.PosSemidef (signedStress m k D) ∧
    Matrix.rank (signedStress m k D) = m - 3

/-- Claim 33825: the infinite regular odd-polygon family is a literal
counterexample to deriving a unit equilateral triangle from the exact
positive equilibrium, PSD stress, and maximal-rank conditions. -/
def claim33825 : Prop :=
  Set.Infinite {m : ℕ | 7 ≤ m ∧ Odd m} ∧
    (∀ m : ℕ, 7 ≤ m → Odd m →
      let k := (m - 1) / 2
      let x := regularPolygon m
      let D := planarDiameter x
      (¬ hasUnitTriangle x) ∧
        strictKKT x ∧
        Matrix.PosSemidef (signedStress m k D) ∧
        Matrix.rank (signedStress m k D) = m - 3 ∧
        stressFeasible m ∧
        ¬ (stressFeasible m → hasUnitTriangle x))

end
end MathlibPlus.Open.ResearchFormalization.StressFeasibilityObstructionClaim33825
