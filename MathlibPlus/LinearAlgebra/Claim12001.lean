-- UNVERIFIED (native-decide): submitted but not kernel-verified, so it is not built and MathlibPlus.lean does not import it. See unverified.txt.
import MathlibPlus.MomentGeometry.RankThreeCounterexample

namespace MathlibPlus.LinearAlgebra.Claim12001

open Matrix

/-- The explicit strictly totally positive rational witness whose folded
 determinant is positive while the radius-three Hall expression is negative. -/
theorem positiveFoldedSignDoesNotImplyHallTransport :
    let D : Matrix (Fin 3) (Fin 3) ℚ := !![1, 0, 0; 0, -1, 0; 0, 0, 1]
    let B : Matrix (Fin 3) (Fin 3) ℚ :=
      !![(4955905958 : ℚ) / 100000000, (474398758 : ℚ) / 100000000,
          (424613702 : ℚ) / 100000000;
         (60278718028 : ℚ) / 100000000, (5892247434 : ℚ) / 100000000,
          (9061660513 : ℚ) / 100000000;
         (3077594537 : ℚ) / 100000000, (301020645 : ℚ) / 100000000,
          (470377566 : ℚ) / 100000000]
    MathlibPlus.MomentGeometry.IsStrictlyTotallyPositive B ∧
      Matrix.det (1 + D * B) =
        (1638748836951503530949933 : ℚ) / 50000000000000000000000 ∧
      1 + Matrix.trace (D * B) = -(36596391 : ℚ) / 10000000 ∧
      B 1 1 > 1 + B 0 0 + B 2 2 := by
  native_decide

end MathlibPlus.LinearAlgebra.Claim12001
