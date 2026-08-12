import Mathlib

namespace MathlibPlus.Combinatorics.PairPathRelaxation

private lemma uniformPrefixSum (n t : ℕ) (hn0 : (n : ℚ) ≠ 0) :
    (∑ s ∈ Finset.range t, (1 : ℚ) / (n : ℚ)) = (t : ℚ) / (n : ℚ) := by
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_one]
  field_simp

private lemma uniformFinSum (n : ℕ) (hn0 : (n : ℚ) ≠ 0) :
    (∑ _i : Fin n, (1 : ℚ) / (n : ℚ)) = 1 := by
  simp [Finset.sum_const, hn0]

private lemma uniformRangeSum (n : ℕ) (hn0 : (n : ℚ) ≠ 0) :
    (∑ t ∈ Finset.range n, (1 : ℚ) / (n : ℚ)) = 1 := by
  rw [uniformPrefixSum n n hn0]
  exact div_self hn0

/-- Claim 47463, feasibility part.  The time coordinate is 0-based: `x` is
uniform on the `n` slots, `X i t` is the prefix through slots `< t`, and `y`
is indexed through the terminal time `n`.  This makes explicit the natural
0-based reading of the source's mixed prefix notation. -/
theorem pairPathUniformFeasible (n : ℕ) (hn : 2 ≤ n) :
    let E := {p : Fin n × Fin n // p.1 < p.2}
    let x : Fin n → ℕ → ℚ := fun _ _ => 1 / (n : ℚ)
    let y : E → ℕ → ℚ := fun _ t => (t : ℚ) / (n : ℚ)
    let X : Fin n → ℕ → ℚ := fun i t =>
      ∑ s ∈ Finset.range t, x i s
    (∀ i, (∑ t ∈ Finset.range n, x i t) = 1) ∧
      (∀ t, t < n → (∑ i : Fin n, x i t) = 1) ∧
      (∀ i j, i < j → ∀ t, t ≤ n → X i t = X j t) ∧
      (∀ p t, t ≤ n →
        0 ≤ y p t ∧ y p t ≤ X p.1.1 t ∧ y p t ≤ X p.1.2 t) ∧
      (∀ p t u, t ≤ u → t ≤ n → u ≤ n → y p t ≤ y p u) ∧
      (∀ p, y p n = 1) := by
  dsimp
  have hn0 : (n : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_two hn))
  have hprefix : ∀ t : ℕ,
      (∑ s ∈ Finset.range t, (1 : ℚ) / (n : ℚ)) = (t : ℚ) / (n : ℚ) := by
    intro t
    exact uniformPrefixSum n t hn0
  have htotal : (∑ t ∈ Finset.range n, (1 : ℚ) / (n : ℚ)) = 1 :=
    uniformRangeSum n hn0
  have hfinite : (∑ _i : Fin n, (1 : ℚ) / (n : ℚ)) = 1 :=
    uniformFinSum n hn0
  constructor
  · intro i
    exact htotal
  constructor
  · intro t ht
    exact hfinite
  constructor
  · intro i j hij t ht
    simp only [hprefix]
  constructor
  · intro p t ht
    have hnonneg : (0 : ℚ) ≤ (t : ℚ) / (n : ℚ) := by positivity
    have hle : (t : ℚ) / (n : ℚ) ≤
        (∑ s ∈ Finset.range t, (1 : ℚ) / (n : ℚ)) := by
      rw [hprefix]
    exact ⟨hnonneg, hle, hle⟩
  constructor
  · intro p t u htu ht hu
    have hden : (0 : ℚ) < n := by positivity
    apply div_le_div_of_nonneg_right
    · exact_mod_cast htu
    · exact le_of_lt hden
  · intro p
    field_simp [hn0]

/-- Claim 47463, objective part.  With `m = n(n-1)/2` pair paths and
amplitude `1/m`, the uniform point has the displayed squared-amplitude
completion objective, including time zero. -/
theorem pairPathUniformObjective (n : ℕ) (hn : 2 ≤ n) :
    let m : ℚ := (n : ℚ) * (n - 1 : ℚ) / 2
    m * (1 / m) ^ 2 *
        (∑ t ∈ Finset.range n, (1 - (t : ℚ) / (n : ℚ))) =
      (n + 1 : ℚ) / ((n : ℚ) * (n - 1 : ℚ)) := by
  dsimp
  have hn0 : (n : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_two hn))
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hnminus : 0 < n - 1 :=
    Nat.sub_pos_of_lt (lt_of_lt_of_le (by norm_num) hn)
  have hnq1 : (1 : ℚ) < (n : ℚ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num) hn)
  have hnminusq : (0 : ℚ) < (n : ℚ) - 1 := by linarith
  have hprod : (0 : ℚ) < (n : ℚ) * (n - 1 : ℚ) :=
    mul_pos (by exact_mod_cast hnpos) hnminusq
  have hmc : (n : ℚ) * (n - 1 : ℚ) / 2 ≠ 0 := by positivity
  have hn1 : (n : ℚ) - 1 ≠ 0 := ne_of_gt hnminusq
  rw [Finset.sum_sub_distrib, Finset.sum_const, ← Finset.sum_div]
  have hsum : (∑ i ∈ Finset.range n, (i : ℚ)) =
      (n : ℚ) * (n - 1 : ℚ) / 2 := by
    rw [← Nat.cast_sum]
    apply (eq_div_iff (by norm_num : (2 : ℚ) ≠ 0)).2
    calc
      (↑(∑ i ∈ Finset.range n, i) : ℚ) * 2 =
          ↑((∑ i ∈ Finset.range n, i) * 2) := by norm_num
      _ = ↑(n * (n - 1)) := by rw [Finset.sum_range_id_mul_two]
      _ = (n : ℚ) * ((n - 1 : ℕ) : ℚ) := by norm_num
      _ = (n : ℚ) * ((n : ℚ) - 1) := by
        rw [Nat.cast_sub (by omega)]
        norm_num
  rw [hsum]
  simp only [Finset.card_range, nsmul_eq_mul, Nat.cast_one]
  field_simp [hn0, hmc, hn1]
  ring

end MathlibPlus.Combinatorics.PairPathRelaxation
