import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.NormNum

namespace MathlibPlus.NumberTheory

/--
Claim 8215 (packet `K-0075`): for a modulus larger than one and a coprime
index, the least positive residue is the quotient-remainder decomposition
`k - N * floor (k / N)`, with positivity supplied by coprimality.
-/
theorem claim8215_least_residue_decomposition
    (N k : ℕ) (hN : 1 < N) (hcop : Nat.Coprime N k) :
    k % N = k - N * (k / N) ∧ 0 < k % N := by
  have hdiv : N * (k / N) + k % N = k := by
    simpa [Nat.add_comm] using (Nat.mod_add_div k N)
  have heq : k % N = k - N * (k / N) := by omega
  refine ⟨heq, ?_⟩
  by_contra hzero
  have hz : k % N = 0 := Nat.eq_zero_of_not_pos hzero
  have hdvd : N ∣ k := by
    use k / N
    omega
  have hg : N ∣ Nat.gcd N k := Nat.dvd_gcd (dvd_refl N) hdvd
  have hgcd : Nat.gcd N k = 1 := hcop
  rw [hgcd] at hg
  exact (Nat.not_dvd_of_pos_of_lt (by omega) hN) hg

end MathlibPlus.NumberTheory
