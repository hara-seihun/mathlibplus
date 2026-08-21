-- UNVERIFIED (native-decide): submitted but not kernel-verified, so it is not built and MathlibPlus.lean does not import it. See unverified.txt.
import Mathlib

namespace MathlibPlus.Combinatorics

/-- Claim 45107: the admissible orbit-type state space for block sizes
`(3, 10, 10)` and one Boolean outside coordinate has cardinality `368`.
The finite types encode the displayed coordinate bounds, and the filter retains
both the source's nonempty condition and its complete-block condition. -/
theorem orbitTypeCard_claim45107 :
    let T : Finset (Fin 4 × Fin 11 × Fin 11 × Bool) :=
      Finset.univ.filter (fun t =>
        (t.1.val ≠ 0 ∨ t.2.1.val ≠ 0 ∨ t.2.2.1.val ≠ 0 ∨ t.2.2.2 = true) ∧
        (t.1.val = 3 ∨ t.2.1.val = 10 ∨ t.2.2.1.val = 10))
    T.card = 368 := by
  native_decide

end MathlibPlus.Combinatorics
