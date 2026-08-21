-- UNVERIFIED (native-decide): submitted but not kernel-verified, so it is not built and MathlibPlus.lean does not import it. See unverified.txt.
import Mathlib

namespace MathlibPlus.Algebra.Claim48665

/-- Exact finite zero-level and jump data from the replay certificate.  The
recurrence and the no-intervening-zero predicate are intentionally not
reconstructed from the prose-only packet. -/
theorem successive_zero_chain_receipt_claim48665 :
    ∃ z : Fin 16 → ℕ,
      z = ![0, 2, 78, 234, 430, 1502, 2942, 6058, 6618, 18910,
        54222, 302467994, 1772665630, 2148845166, 5145362666,
        129465909326] ∧
      z 11 - z 10 = 302413772 ∧
      z 15 - z 14 = 124320546660 := by
  refine ⟨![0, 2, 78, 234, 430, 1502, 2942, 6058, 6618, 18910,
    54222, 302467994, 1772665630, 2148845166, 5145362666,
    129465909326], rfl, ?_, ?_⟩
  · native_decide
  · native_decide

end MathlibPlus.Algebra.Claim48665
