import Mathlib

namespace MathlibPlus.Analysis.Claim10680

/--
RECEIPT: exact rational sign data recorded in admitted claim 10680.  The
source-specific kernels `K₂`, `K₃`, and `K₄` are not defined in the packet, so
this theorem deliberately records only their displayed numerical values and
signs rather than pretending to identify those values with a Lean function.
-/
theorem rankFourSingletonSignReversal_arithmeticReceipt_claim10680 :
    (0 < (575 / 512 : ℚ)) ∧
      (0 < (49575 / 131072 : ℚ)) ∧
        ((-3901 / 16777216 : ℚ) < 0) := by
  norm_num

end MathlibPlus.Analysis.Claim10680
