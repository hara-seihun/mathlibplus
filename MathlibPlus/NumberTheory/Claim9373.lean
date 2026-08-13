import Mathlib

namespace MathlibPlus.NumberTheory.Claim9373

open scoped BigOperators

/-- The finite coefficient sum in claim 9373 is the displayed remainder.
The analytic Dirichlet-series carrier is intentionally not totalized here. -/
theorem partialSum_eq_remainder_claim9373 (N q : ℕ) :
    ((Finset.range N.succ).filter (fun n => n ≠ 0)).sum
        (fun n => (1 : ℤ) - (q : ℤ) * if q ∣ n then 1 else 0) =
      (N : ℤ) - (q : ℤ) * ((N / q : ℕ) : ℤ) ∧
    (N : ℤ) - (q : ℤ) * ((N / q : ℕ) : ℤ) = (N % q : ℤ) := by
  classical
  let s : Finset ℕ := (Finset.range N.succ).filter (fun n => n ≠ 0)
  have hs_card : s.card = N := by
    simp [s, Finset.filter_ne', Finset.card_erase_of_mem]
  have hmult : (s.filter (fun n => q ∣ n)).card = N / q := by
    simpa [s, Finset.filter_filter, and_assoc, and_left_comm, and_comm] using
      (Nat.card_multiples' N q)
  have hsum :
      s.sum (fun n => if q ∣ n then (1 : ℤ) else 0) =
        ((s.filter (fun n => q ∣ n)).card : ℤ) := by
    rw [← Finset.sum_filter]
    simp
  constructor
  · change s.sum (fun n => (1 : ℤ) - (q : ℤ) *
        (if q ∣ n then 1 else 0)) = _
    calc
      s.sum (fun n => (1 : ℤ) - (q : ℤ) *
          (if q ∣ n then 1 else 0)) =
          (s.sum (fun _ => (1 : ℤ))) -
            (s.sum (fun n => (q : ℤ) * (if q ∣ n then 1 else 0))) := by
        exact Finset.sum_sub_distrib (s := s)
          (fun _ => (1 : ℤ))
          (fun n => (q : ℤ) * (if q ∣ n then 1 else 0))
      _ = (N : ℤ) - (q : ℤ) *
          s.sum (fun n => if q ∣ n then (1 : ℤ) else 0) := by
        rw [Finset.sum_const, hs_card]
        rw [nsmul_eq_mul, mul_one, Finset.mul_sum]
      _ = (N : ℤ) - (q : ℤ) * ((N / q : ℕ) : ℤ) := by
        rw [hsum, hmult]
  · have hle : q * (N / q) ≤ N := Nat.mul_div_le N q
    have hcast := congrArg (fun n : ℕ => (n : ℤ))
      (Nat.mod_eq_sub_mul_div (x := N) (k := q))
    rw [Nat.cast_sub hle] at hcast
    exact hcast.symm

end MathlibPlus.NumberTheory.Claim9373
