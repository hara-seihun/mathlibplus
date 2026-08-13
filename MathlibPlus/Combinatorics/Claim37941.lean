import Mathlib

namespace MathlibPlus.Combinatorics

/--
Arithmetic part of Claim 37941's inverse-atom Burnside certificate.  The
actual automorphism action and weighted fixed-set computation remain explicit
fidelity boundaries.
-/
theorem claim37941_burnsideArithmetic :
    (1008 : ℕ) = 2 * 504 ∧
      Fintype.card (Fin 39) = 39 ∧
      679991760 = 504 * 1349190 := by
  norm_num [Fintype.card_fin]

end MathlibPlus.Combinatorics
