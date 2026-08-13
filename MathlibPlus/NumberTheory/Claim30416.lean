import Mathlib

namespace MathlibPlus.NumberTheory

/--
The arithmetic fixed-point obstruction used in Claim 30416.  The prime and
large-prime hypotheses are retained exactly; the block orbit and kernel
carriers remain outside this arithmetic lemma.
-/
theorem claim30416_primeCannotDivideFour
    {p : ℕ} (hp : Nat.Prime p) (hp5 : 5 ≤ p) : ¬ p ∣ 4 := by
  intro hdiv
  have hle : p ≤ 4 := Nat.le_of_dvd (by norm_num) hdiv
  omega

end MathlibPlus.NumberTheory
