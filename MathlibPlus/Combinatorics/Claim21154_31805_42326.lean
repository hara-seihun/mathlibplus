import Mathlib.NumberTheory.Chebyshev

namespace MathlibPlus.Combinatorics.Claim21154

/-- Claim 21154: the two exact signed mass pairs reported for the first and
final merges, including their zero-sum property. -/
theorem firstAndFinalMergeMasses_claim21154 :
    let first : ℤ × ℤ := (72, -72)
    let final : ℤ × ℤ := (2520, -2520)
    first = (72, -72) ∧ final = (2520, -2520) ∧
      first.1 + first.2 = 0 ∧ final.1 + final.2 = 0 := by
  norm_num

end MathlibPlus.Combinatorics.Claim21154

namespace MathlibPlus.Combinatorics.Claim31805

/-- Claim 31805: the displayed residual-row valency distribution, with its
reported total of 190 rows. -/
theorem residualValencyDistribution_claim31805 :
    let valencies : Fin 4 → ℕ := ![11, 12, 13, 14]
    let counts : Fin 4 → ℕ := ![33, 46, 47, 64]
    valencies 0 = 11 ∧ valencies 1 = 12 ∧ valencies 2 = 13 ∧ valencies 3 = 14 ∧
      counts 0 = 33 ∧ counts 1 = 46 ∧ counts 2 = 47 ∧ counts 3 = 64 ∧
      (∑ i, counts i) = 190 := by
  norm_num [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three]

end MathlibPlus.Combinatorics.Claim31805

namespace MathlibPlus.Combinatorics.Claim42326

/-- Claim 42326: for each displayed threshold index, the reported ideal size
is a proper majority of a 76-node construction. -/
theorem thresholdRootsMajorityHeavy_claim42326 :
    ∀ a : ℕ, 1 ≤ a → a ≤ 8 →
      30 + 19 + a + a = 49 + 2 * a ∧
      76 / 2 < 49 + 2 * a ∧ 49 + 2 * a < 76 := by
  intro a ha₁ ha₈
  omega
