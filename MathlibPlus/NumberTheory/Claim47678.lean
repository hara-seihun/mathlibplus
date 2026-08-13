import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic

namespace MathlibPlus.NumberTheory

/-!
Formalization of the factorial-valuation block identity in admitted claim 47678.
The source's `v_p` is represented by `padicValNat`; the prime hypothesis supplies
its `Fact` instance.  The displayed finite geometric sum is written as a
`Finset.range` sum, with the source condition `a ≥ 1` retained explicitly.
-/

/-- For a prime `p`, the valuation of `(p^a M)!` splits into the valuation of
`M!` and the first `a` powers of `p`, as in claim 47678. -/
theorem factorialValuationBlock_claim47678
    {p : ℕ} (hp : p.Prime) (a M : ℕ) (_ha : 1 ≤ a) :
    padicValNat p (Nat.factorial (p ^ a * M)) =
      M * ∑ i ∈ Finset.range a, p ^ i +
        padicValNat p (Nat.factorial M) := by
  haveI : Fact p.Prime := ⟨hp⟩
  clear _ha
  induction a with
  | zero => simp
  | succ a ih =>
      rw [show p ^ (Nat.succ a) * M = p * (p ^ a * M) by
        rw [pow_succ]
        ac_rfl]
      rw [padicValNat_factorial_mul, ih]
      rw [Finset.sum_range_succ]
      simp [Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
        Nat.mul_comm]

end MathlibPlus.NumberTheory
