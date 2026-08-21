-- UNVERIFIED (native-decide): submitted but not kernel-verified, so it is not built and MathlibPlus.lean does not import it. See unverified.txt.
import Mathlib

namespace MathlibPlus.Combinatorics

/--
Claim 39429: a fixed-slice profile is determined by a nonzero support point
of `Fin 3 → Fin 3` and a nonzero top-carry value in `Fin 3`.
-/
theorem fixedSliceProfileCount :
    Fintype.card
        ({x : Fin 3 → Fin 3 // x ≠ 0} × {c : Fin 3 // c ≠ 0}) = 52 := by
  native_decide

end MathlibPlus.Combinatorics
