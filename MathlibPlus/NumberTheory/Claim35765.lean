import MathlibPlus.Basic

namespace MathlibPlus.NumberTheory

open scoped BigOperators

private def weight (j : ℕ) : ℚ := (j : ℚ) / 2 ^ j

private lemma weight_succ_lt (k : ℕ) (hk : 2 ≤ k) :
    weight (k + 1) < weight k := by
  dsimp [weight]
  apply (div_lt_div_iff₀ (by positivity) (by positivity)).2
  rw [pow_succ]
  norm_num
  have hkq : (2 : ℚ) ≤ k := by exact_mod_cast hk
  nlinarith [show (0 : ℚ) < 2 ^ k by positivity]

private lemma weight_lt_of_two_le_lt {a b : ℕ} (ha : 2 ≤ a) (hab : a < b) :
    weight b < weight a := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_lt hab)
  have hd : 0 < d := by omega
  obtain ⟨e, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hd)
  induction e with
  | zero =>
      simpa using weight_succ_lt a ha
  | succ e ih =>
      have hstep : weight (a + (e + 1) + 1) < weight (a + (e + 1)) := by
        apply weight_succ_lt
        omega
      exact hstep.trans (ih (by omega) (by omega))

/-- In the weighted binary representation `w(j)=j/2^j`, a positive finite
representation of `w(n)` with `n≥3` cannot use an index at or below `n`.
The finite set supplies distinctness, and `hpos` records the source's
requirement that every used summand is positive. -/
theorem claim35765_usedIndicesAboveTarget
    (n : ℕ) (hn : 3 ≤ n) (s : Finset ℕ) (hs : n ∉ s)
    (hpos : ∀ j ∈ s, 0 < weight j)
    (hsum : (∑ j ∈ s, weight j) = weight n) :
    ∀ j ∈ s, n < j := by
  intro j hj
  by_contra hjn
  have hjle : j ≤ n := by omega
  have hjne : j ≠ n := by
    intro h
    apply hs
    simpa [h] using hj
  have hjlt : j < n := by omega
  have hstrict : weight n < weight j := by
    by_cases hj2 : 2 ≤ j
    · exact weight_lt_of_two_le_lt hj2 hjlt
    · have hjsmall : j < 2 := by omega
      have hjzero : j ≠ 0 := by
        intro hzero
        subst j
        have h := hpos 0 hj
        norm_num [weight] at h
      have hjone : j = 1 := by omega
      subst j
      have hn2 : weight n < weight 2 :=
        weight_lt_of_two_le_lt (by omega) (by omega)
      exact hn2.trans_eq (by norm_num [weight])
  have hle : weight j ≤ ∑ k ∈ s, weight k :=
    Finset.single_le_sum (fun k hk => le_of_lt (hpos k hk)) hj
  rw [hsum] at hle
  exact (not_lt_of_ge hle) hstrict

end MathlibPlus.NumberTheory
