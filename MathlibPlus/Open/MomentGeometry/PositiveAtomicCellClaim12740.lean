import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace MathlibPlus.Open.MomentGeometry

/-- Claim 12740: every finite weighted power matrix with strictly increasing
positive nodes and positive row weights is strictly totally positive. -/
def positiveAtomicCellMatricesStrictlyTotallyPositive_claim12740 : Prop :=
  ∀ (m n : ℕ) (x : Fin m → ℝ) (w : Fin m → ℝ),
    (∀ i, 0 < x i) ∧ StrictMono x ∧ (∀ i, 0 < w i) →
      ∀ k : Fin (min m n),
        ∀ rows : Fin (k.1 + 1) → Fin m, StrictMono rows →
          ∀ cols : Fin (k.1 + 1) → Fin n, StrictMono cols →
            0 < Matrix.det (fun i j : Fin (k.1 + 1) =>
              w (rows i) * x (rows i) ^ (cols j : ℕ) /
                (Nat.factorial (2 * (cols j : ℕ)) : ℝ))

end MathlibPlus.Open.MomentGeometry
