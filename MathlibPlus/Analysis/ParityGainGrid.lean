import Mathlib.Tactic

namespace MathlibPlus.Analysis

/--
Formalization of the missing-parity subclaim in admitted claim 8045 (K-0061).
The positive block's gain grid is represented by the integer values
`Mstar - 1 - 2*k` for `k < Mstar`.
-/
theorem positiveBlockCannotTieMissingParity
    (Mstar Nstar : ℕ) (_hMstar : 0 < Mstar)
    (hparity : Nstar % 2 ≠ Mstar % 2) :
    ¬ ∃ k : ℕ, k < Mstar ∧
      (Nstar : ℤ) - 1 = (Mstar : ℤ) - 1 - 2 * (k : ℤ) := by
  omega

end MathlibPlus.Analysis
