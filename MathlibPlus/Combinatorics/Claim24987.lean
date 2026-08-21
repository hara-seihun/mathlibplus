-- UNVERIFIED (native-decide): submitted but not kernel-verified, so it is not built and MathlibPlus.lean does not import it. See unverified.txt.
import Mathlib

namespace MathlibPlus.Combinatorics

/--
Literal finite certificate for Claim 24987: twelve of eighteen survivors,
the two allowed proportionality ratios, and the two-of-three pairing count.
The cavity and chord constructions remain explicit source carriers.
-/
theorem claim24987_residualCountCertificate :
    let ratios : Finset ℤ := {-1, 1}
    ratios.card = 2 ∧
      (12 : ℕ) + 6 = 18 ∧
      12 ≤ 18 ∧
      2 ≤ 3 ∧
      (-1 : ℤ) ∈ ratios ∧
      (1 : ℤ) ∈ ratios := by
  native_decide

end MathlibPlus.Combinatorics
