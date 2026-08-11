import MathlibPlus.Basic

open scoped BigOperators

namespace MathlibPlus.Algebra.BinaryCarry

/-- Claim 35657: the carry expression attached to a reduced positive rational
and binary digits is integral at every finite prefix. -/
theorem binaryCarry_integrality_claim35657
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hcop : Nat.Coprime p q)
    (d : ℕ → ℕ) (hd : ∀ j, d j ≤ 1) :
    let r : ℕ → ℚ := fun k =>
      (q : ℚ) * 2 ^ k *
        ((p : ℚ) / q -
          ∑ j ∈ Finset.range k,
            ((j + 1 : ℕ) : ℚ) * (d j : ℚ) / 2 ^ (j + 1))
    (∀ k, ∃ z : ℤ, r k = z) ∧ r 0 = p := by
  let r : ℕ → ℚ := fun k =>
    (q : ℚ) * 2 ^ k *
      ((p : ℚ) / q -
        ∑ j ∈ Finset.range k,
          ((j + 1 : ℕ) : ℚ) * (d j : ℚ) / 2 ^ (j + 1))
  have hq0 : (q : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hq)
  change (∀ k, ∃ z : ℤ, r k = z) ∧ r 0 = p
  have hrec (k : ℕ) :
      r (k + 1) = 2 * r k - (q : ℚ) * (k + 1) * d k := by
    dsimp [r]
    rw [Finset.sum_range_succ]
    rw [pow_succ]
    field_simp [hq0]
    norm_num [Nat.cast_add, Nat.cast_one]
    ring
  have hzero : r 0 = (p : ℚ) := by
    dsimp [r]
    field_simp [hq0]
    ring
  constructor
  · intro k
    induction k with
    | zero =>
        exact ⟨(p : ℤ), by simpa [hzero]⟩
    | succ k ih =>
        rcases ih with ⟨z, hz⟩
        refine ⟨2 * z - (q : ℤ) * (k + 1) * (d k : ℤ), ?_⟩
        rw [hrec, hz]
        norm_cast
  · exact hzero

end MathlibPlus.Algebra.BinaryCarry
