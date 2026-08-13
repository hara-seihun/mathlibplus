import Mathlib

namespace MathlibPlus.Algebra.Claim51901

private theorem sum_coin (A : ℤ) (k : ℕ) :
    ∑ i ∈ Finset.range k, (A - (i : ℤ) - 2) * (2 : ℤ) ^ i =
      (A - (k : ℤ)) * (2 : ℤ) ^ k - A := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

/-- The displayed coin-sum and gap identities from claim 51901.  The
packet's excerpt leaves the definition and ambient domain of `c` implicit;
this exact algebraic core makes the displayed sequence explicit and keeps
that missing convention visible as a hypothesis. -/
theorem coinSumAndGap_claim51901
    (A : ℤ) (c : ℕ → ℤ)
    (hc : ∀ i : ℕ, c i = (A - (i : ℤ) - 2) * (2 : ℤ) ^ i) :
    ∀ k : ℕ,
      (∑ i ∈ Finset.range k, c i) =
          (A - (k : ℤ)) * (2 : ℤ) ^ k - A ∧
        c k - ∑ i ∈ Finset.range k, c i =
          A - (2 : ℤ) ^ (k + 1) := by
  intro k
  have hsum :
      (∑ i ∈ Finset.range k, c i) =
        ∑ i ∈ Finset.range k, (A - (i : ℤ) - 2) * (2 : ℤ) ^ i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hc]
  constructor
  · exact hsum.trans (sum_coin A k)
  · rw [hc k, hsum, sum_coin A k]
    push_cast
    ring

end MathlibPlus.Algebra.Claim51901
