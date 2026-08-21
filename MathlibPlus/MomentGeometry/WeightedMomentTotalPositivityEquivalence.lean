import Mathlib
import MathlibPlus.Open.MomentCurve.TotalPositivity
import MathlibPlus.Open.MomentGeometry.PositiveAtomicCellClaim12740

namespace MathlibPlus.MomentGeometry

/-- The two weighted moment-curve strict-total-positivity nodes differ only
in how they encode an available ordered square minor. -/
theorem strictTotalPositivityWeightedMomentTable_iff_positiveAtomicCellMatrices :
    MathlibPlus.Open.MomentCurve.strictTotalPositivityWeightedMomentTable ↔
      MathlibPlus.Open.MomentGeometry.positiveAtomicCellMatricesStrictlyTotallyPositive_claim12740 := by
  unfold MathlibPlus.Open.MomentCurve.strictTotalPositivityWeightedMomentTable
    MathlibPlus.Open.MomentGeometry.positiveAtomicCellMatricesStrictlyTotallyPositive_claim12740
  constructor
  · intro h m n x w hdata k rows hrows cols hcols
    let rows' : Fin (k.1 + 1) ↪o Fin m :=
      OrderEmbedding.ofStrictMono rows hrows
    let cols' : Fin (k.1 + 1) ↪o Fin n :=
      OrderEmbedding.ofStrictMono cols hcols
    simpa [rows', cols'] using
      h m n (k.1 + 1) x w rows' cols' hdata.1 hdata.2.1 hdata.2.2
  · intro h m n r x w rows cols hx hmono hw
    cases r with
    | zero =>
        have hdet : Matrix.det (fun i j : Fin 0 =>
            w (rows i) * x (rows i) ^ (cols j : Fin n).val /
              (((2 * (cols j : Fin n).val).factorial : ℕ) : ℝ)) = (1 : ℝ) :=
          Matrix.det_fin_zero
        rw [hdet]
        norm_num
    | succ r =>
        have hrm : r + 1 ≤ m := by
          simpa only [Fintype.card_fin] using
            Fintype.card_le_of_injective rows rows.injective
        have hrn : r + 1 ≤ n := by
          simpa only [Fintype.card_fin] using
            Fintype.card_le_of_injective cols cols.injective
        have hk : r < min m n := by omega
        exact h m n x w ⟨hx, hmono, hw⟩ ⟨r, hk⟩
          rows rows.strictMono cols cols.strictMono

end MathlibPlus.MomentGeometry
