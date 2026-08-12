import Mathlib

namespace MathlibPlus.Algebra.Claim17460

/-- The componentwise Plücker-current identity from claim 17460.  The grading
operator is represented by multiplication by the index, and the source's
sequence carrier is otherwise left abstract. -/
theorem componentwise_plucker_current_claim17460
    {K : Type*} [Field K] [CharZero K]
    (h q : ℕ → K)
    (hq : ∀ n, q n = 2 * (n : K) * h n)
    (a b : ℕ) :
    ((b : K) - (a : K)) * h a * h b =
      (1 / 2 : K) * (h a * q b - q a * h b) := by
  rw [hq a, hq b]
  ring

end MathlibPlus.Algebra.Claim17460
