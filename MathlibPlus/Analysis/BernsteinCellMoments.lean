import Mathlib

namespace MathlibPlus.Analysis.BernsteinCellMoments

noncomputable section

/--
The Bernstein cell-moment coefficient from admitted claim 18107.  The cell
index is a positive natural, which is the positive-cell convention needed for
the displayed ordinary interval integral to have its intended real-power
semantics at every sample exponent.
-/
def bernsteinCellMomentCoefficient (n : ℕ+) (m : ℕ) : ℝ :=
  ∫ x : ℝ in (n : ℝ)..(n + 1 : ℝ),
    (x - n) * x ^ (-3 / 2 : ℝ) * (1 - x ^ (-2 : ℝ)) ^ m

private lemma rpow_nat_mul (x : ℝ) (hx : 0 < x) (k : ℕ) :
    x ^ ((-3 / 2 : ℝ) - 2 * (k : ℝ)) =
      x ^ (-3 / 2 : ℝ) * (x ^ (-2 : ℝ)) ^ k := by
  have harg : (-3 / 2 : ℝ) - 2 * (k : ℝ) =
      (-3 / 2 : ℝ) + (-2 : ℝ) * (k : ℝ) := by ring
  rw [harg, Real.rpow_add hx]
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul (le_of_lt hx)]

private lemma binomial_one_sub (y : ℝ) (m : ℕ) :
    (1 - y) ^ m =
      ∑ k ∈ Finset.range (m + 1),
        (-1 : ℝ) ^ k * (m.choose k : ℝ) * y ^ k := by
  rw [sub_pow]
  simp only [one_pow]
  rw [← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro k hk
  have hk_le : k ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hmk : m + 1 - 1 - k = m - k := by omega
  have hpow : m - (m - k) = k := by omega
  rw [hmk, hpow, Nat.choose_symm hk_le]
  have hparity : (m - k + m) % 2 = k % 2 := by omega
  rw [neg_one_pow_eq_pow_mod_two (m - k + m),
    neg_one_pow_eq_pow_mod_two k, hparity]
  simp
  ring

/-- The finite alternating-difference identity from admitted claim 18113. -/
theorem finiteAlternatingDifference (n : ℕ+) (m : ℕ) :
    bernsteinCellMomentCoefficient n m =
      ∑ k ∈ Finset.range (m + 1),
        (-1 : ℝ) ^ k * (m.choose k : ℝ) *
          (∫ x : ℝ in (n : ℝ)..(n + 1 : ℝ),
            (x - n) * x ^ ((-3 / 2 : ℝ) - 2 * (k : ℝ))) := by
  unfold bernsteinCellMomentCoefficient
  have hn : (0 : ℝ) < (n : ℝ) := by exact_mod_cast n.property
  have hle : (n : ℝ) ≤ (n + 1 : ℝ) := by norm_num
  have hpos : ∀ x : ℝ, x ∈ Set.uIcc (n : ℝ) (n + 1 : ℝ) → 0 < x := by
    intro x hx
    rw [Set.uIcc_of_le hle] at hx
    exact lt_of_lt_of_le hn hx.1
  let f : ℕ → ℝ → ℝ := fun k x =>
    (-1 : ℝ) ^ k * (m.choose k : ℝ) *
      ((x - (n : ℝ)) * x ^ ((-3 / 2 : ℝ) - 2 * (k : ℝ)))
  have hf : ∀ k ∈ Finset.range (m + 1),
      IntervalIntegrable (f k) MeasureTheory.volume (n : ℝ) (n + 1 : ℝ) := by
    intro k hk
    apply ContinuousOn.intervalIntegrable
    have h_id : ContinuousOn (fun x : ℝ => x) (Set.uIcc (n : ℝ) (n + 1 : ℝ)) :=
      continuousOn_id
    have hpow : ContinuousOn
        (fun x : ℝ => x ^ ((-3 / 2 : ℝ) - 2 * (k : ℝ)))
        (Set.uIcc (n : ℝ) (n + 1 : ℝ)) := by
      apply h_id.rpow_const
      intro x hx
      exact Or.inl (ne_of_gt (hpos x hx))
    have hbase : ContinuousOn
        (fun x : ℝ => (x - (n : ℝ)) *
          x ^ ((-3 / 2 : ℝ) - 2 * (k : ℝ)))
        (Set.uIcc (n : ℝ) (n + 1 : ℝ)) :=
      (h_id.sub continuousOn_const).mul hpow
    exact hbase.const_mul ((-1 : ℝ) ^ k * (m.choose k : ℝ))
  have hsum :
      (∫ x : ℝ in (n : ℝ)..(n + 1 : ℝ), ∑ k ∈ Finset.range (m + 1), f k x) =
        ∑ k ∈ Finset.range (m + 1),
          ∫ x : ℝ in (n : ℝ)..(n + 1 : ℝ), f k x := by
    apply intervalIntegral.integral_finsetSum
    intro k hk
    exact hf k hk
  calc
    (∫ x : ℝ in (n : ℝ)..(n + 1 : ℝ),
        (x - (n : ℝ)) * x ^ (-3 / 2 : ℝ) * (1 - x ^ (-2 : ℝ)) ^ m) =
        ∫ x : ℝ in (n : ℝ)..(n + 1 : ℝ), ∑ k ∈ Finset.range (m + 1), f k x := by
      apply intervalIntegral.integral_congr
      intro x hx
      have hxpos := hpos x hx
      dsimp [f]
      rw [binomial_one_sub (x ^ (-2 : ℝ)) m]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [rpow_nat_mul x hxpos k]
      ring
    _ = ∑ k ∈ Finset.range (m + 1),
          ∫ x : ℝ in (n : ℝ)..(n + 1 : ℝ), f k x := hsum
    _ = ∑ k ∈ Finset.range (m + 1),
          (-1 : ℝ) ^ k * (m.choose k : ℝ) *
            (∫ x : ℝ in (n : ℝ)..(n + 1 : ℝ),
              (x - (n : ℝ)) * x ^ ((-3 / 2 : ℝ) - 2 * (k : ℝ))) := by
      apply Finset.sum_congr rfl
      intro k hk
      dsimp [f]
      rw [intervalIntegral.integral_const_mul]

end
end MathlibPlus.Analysis.BernsteinCellMoments
