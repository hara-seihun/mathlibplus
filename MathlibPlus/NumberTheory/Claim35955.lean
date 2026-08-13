import Mathlib

namespace MathlibPlus.NumberTheory.Claim35955

open scoped BigOperators

/-- The interval remainder in the natural-shift/rational-normalization convention.
The source writes floors and `N / p`; here the nonnegative floor terms are represented
by natural quotients and the normalization term is rational. -/
def intervalRemainder (p N t : ℕ) : ℚ :=
  (((t + N) / p : ℕ) : ℚ) - ((t / p : ℕ) : ℚ) - (N : ℚ) / (p : ℚ)

private lemma quotient_add_split (p N t : ℕ) (hp : 0 < p) :
    (t + N) / p = t / p + N / p + (t % p + N % p) / p := by
  have ht : p * (t / p) + t % p = t := Nat.div_add_mod t p
  have hN : p * (N / p) + N % p = N := Nat.div_add_mod N p
  have hsum : t + N = (t % p + N % p) + p * (t / p + N / p) := by
    calc
      t + N = (p * (t / p) + t % p) + (p * (N / p) + N % p) := by rw [ht, hN]
      _ = (t % p + N % p) + p * (t / p + N / p) := by ring
  rw [hsum]
  rw [show (t % p + N % p) + p * (t / p + N / p) =
      (t % p + N % p) + p * (t / p + N / p) by rfl]
  rw [Nat.add_mul_div_left _ _ hp]
  simp only [Nat.add_comm, Nat.add_assoc]

private lemma rational_div_split (p N : ℕ) (hp : 0 < p) :
    (N : ℚ) / (p : ℚ) = ((N / p : ℕ) : ℚ) + ((N % p : ℕ) : ℚ) / (p : ℚ) := by
  have hN : p * (N / p) + N % p = N := Nat.div_add_mod N p
  have hNq : (N : ℚ) = (p : ℚ) * ((N / p : ℕ) : ℚ) + ((N % p : ℕ) : ℚ) := by
    exact_mod_cast hN.symm
  rw [hNq]
  field_simp [ne_of_gt hp]

private lemma carry_quotient (p r b : ℕ) (hp : 0 < p)
    (hr : r < p) (hb : b < p) :
    (r + b) / p = if p ≤ r + b then 1 else 0 := by
  by_cases h : p ≤ r + b
  · have hlt : r + b - p < p := by omega
    have hrepr : r + b = (r + b - p) + p := by omega
    rw [if_pos h, hrepr]
    rw [show (r + b - p) + p = (r + b - p) + p * 1 by simp]
    rw [Nat.add_mul_div_left _ _ hp]
    simp [Nat.div_eq_of_lt hlt]
  · have hlt : r + b < p := by omega
    rw [if_neg h, Nat.div_eq_of_lt hlt]

/-- Exact residue formula for the interval floor remainder in claim 35955. -/
theorem intervalRemainder_eq_residue
    (p N t : ℕ) (hp : Nat.Prime p) :
    intervalRemainder p N t =
      (if N % p = 0 then 0
       else if p - N % p ≤ t % p then 1 else 0) -
        ((N % p : ℕ) : ℚ) / (p : ℚ) := by
  have hp0 : 0 < p := hp.pos
  have hr : t % p < p := Nat.mod_lt _ hp0
  have hb : N % p < p := Nat.mod_lt _ hp0
  rw [intervalRemainder, quotient_add_split p N t hp0,
    rational_div_split p N hp0]
  by_cases hb0 : N % p = 0
  · simp [hb0, Nat.div_eq_of_lt hr]
  · rw [if_neg hb0]
    have hcarry := carry_quotient p (t % p) (N % p) hp0 hr hb
    rw [hcarry]
    have hcond : p ≤ t % p + N % p ↔ p - N % p ≤ t % p := by
      omega
    by_cases hthreshold : p - N % p ≤ t % p
    · simp [hthreshold, hcond] <;> ring
    · simp [hthreshold, hcond]

/-- When the interval length is a multiple of the prime modulus, every shift has
zero remainder. -/
theorem intervalRemainder_zero_of_dvd_claim35955
    (p N t : ℕ) (hp : Nat.Prime p) (hdiv : p ∣ N) :
    intervalRemainder p N t = 0 := by
  have hmod : N % p = 0 := Nat.mod_eq_zero_of_dvd hdiv
  rw [intervalRemainder_eq_residue p N t hp]
  simp [hmod]

/-- For a nonzero residue, the top value of the remainder is attained exactly
on the indicated residue classes. -/
theorem intervalRemainder_maximizer_iff_claim35955
    (p N t : ℕ) (hp : Nat.Prime p) (hb : 0 < N % p) :
    intervalRemainder p N t =
        1 - ((N % p : ℕ) : ℚ) / (p : ℚ) ↔
      p - N % p ≤ t % p := by
  rw [intervalRemainder_eq_residue p N t hp]
  have hcond : p ≤ t % p + N % p ↔ p - N % p ≤ t % p := by
    have hlt : N % p < p := Nat.mod_lt _ hp.pos
    omega
  have hb0 : N % p ≠ 0 := Nat.ne_of_gt hb
  by_cases h : p - N % p ≤ t % p
  · simp [hb0, h]
  · simp [hb0, h] <;> linarith

/-- The indicated maximizing residue classes have exactly `N mod p` elements. -/
theorem maximizing_residue_card_claim35955
    (p N : ℕ) (hp : Nat.Prime p) (hb : 0 < N % p) :
    ((Finset.range p).filter (fun r => p - N % p ≤ r)).card = N % p := by
  have hlt : N % p < p := Nat.mod_lt _ hp.pos
  have hset :
      (Finset.range p).filter (fun r => p - N % p ≤ r) =
        Finset.Ico (p - N % p) p := by
    apply Finset.ext
    intro r
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [hset, Nat.card_Ico]
  omega

/-- The residue formula also gives the asserted upper envelope. -/
theorem intervalRemainder_le_max_claim35955
    (p N t : ℕ) (hp : Nat.Prime p) (_hb : 0 < N % p) :
    intervalRemainder p N t ≤
        1 - ((N % p : ℕ) : ℚ) / (p : ℚ) := by
  rw [intervalRemainder_eq_residue p N t hp]
  split_ifs <;> norm_num <;> linarith

end MathlibPlus.NumberTheory.Claim35955
