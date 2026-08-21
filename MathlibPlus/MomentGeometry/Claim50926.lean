-- UNVERIFIED (native-decide): submitted but not kernel-verified, so it is not built and MathlibPlus.lean does not import it. See unverified.txt.
import MathlibPlus.MomentGeometry.RankThreeCounterexample

namespace MathlibPlus.Open.MomentGeometry

/-- Claim 50926, retaining the packet's exact terminating-decimal matrix and
both displayed determinant values.  The two values are inconsistent; the
ordinary namespace below records the corrected determinant and disproof. -/
def claim50926 : Prop :=
  let B : Matrix (Fin 3) (Fin 3) ℚ := !![
    4955905958 / 100000000, 474398758 / 100000000, 424613702 / 100000000;
    60278718028 / 100000000, 5892247434 / 100000000, 9061660613 / 100000000;
    3077594537 / 100000000, 301020645 / 100000000, 470377566 / 100000000]
  let D : Matrix (Fin 3) (Fin 3) ℚ := !![
    1, 0, 0;
    0, -1, 0;
    0, 0, 1]
  MathlibPlus.MomentGeometry.IsStrictlyTotallyPositive B ∧
    B 1 1 - 1 - B 0 0 - B 2 2 = 36596391 / 10000000 ∧
    Matrix.det (1 + D * B) =
      1638748836951503530949933 / 50000000000000000000000 ∧
    0 < Matrix.det (1 + D * B)

end MathlibPlus.Open.MomentGeometry

namespace MathlibPlus.MomentGeometry

/-- The valid strictly-TP, Hall-defect, and positive-folded-determinant core
of claim 50926. -/
theorem claim50926_validCore :
    let B : Matrix (Fin 3) (Fin 3) ℚ := !![
      4955905958 / 100000000, 474398758 / 100000000, 424613702 / 100000000;
      60278718028 / 100000000, 5892247434 / 100000000, 9061660613 / 100000000;
      3077594537 / 100000000, 301020645 / 100000000, 470377566 / 100000000]
    let D : Matrix (Fin 3) (Fin 3) ℚ := !![
      1, 0, 0;
      0, -1, 0;
      0, 0, 1]
    IsStrictlyTotallyPositive B ∧
      B 1 1 - 1 - B 0 0 - B 2 2 = 36596391 / 10000000 ∧
      0 < Matrix.det (1 + D * B) := by
  native_decide

/-- Exact recomputation of the folded determinant for the displayed matrix. -/
theorem claim50926_actualFoldedDeterminant :
    let B : Matrix (Fin 3) (Fin 3) ℚ := !![
      4955905958 / 100000000, 474398758 / 100000000, 424613702 / 100000000;
      60278718028 / 100000000, 5892247434 / 100000000, 9061660613 / 100000000;
      3077594537 / 100000000, 301020645 / 100000000, 470377566 / 100000000]
    let D : Matrix (Fin 3) (Fin 3) ℚ := !![
      1, 0, 0;
      0, -1, 0;
      0, 0, 1]
    Matrix.det (1 + D * B) =
      1638749146576736311539253 / 50000000000000000000000 := by
  native_decide

/-- The packet's asserted folded determinant is false for its own displayed
matrix, so the exact ledger formalization is disprovable. -/
theorem not_claim50926 : ¬ MathlibPlus.Open.MomentGeometry.claim50926 := by
  intro h
  have heq := h.2.2.1
  have hactual : Matrix.det
      (1 + (!![
        1, 0, 0;
        0, -1, 0;
        0, 0, 1] : Matrix (Fin 3) (Fin 3) ℚ) *
        !![
          4955905958 / 100000000, 474398758 / 100000000, 424613702 / 100000000;
          60278718028 / 100000000, 5892247434 / 100000000, 9061660613 / 100000000;
          3077594537 / 100000000, 301020645 / 100000000, 470377566 / 100000000]) =
      1638749146576736311539253 / 50000000000000000000000 := by
    native_decide
  have hvalues :
      (1638748836951503530949933 / 50000000000000000000000 : ℚ) =
        1638749146576736311539253 / 50000000000000000000000 := by
    exact heq.symm.trans hactual
  norm_num at hvalues

end MathlibPlus.MomentGeometry
