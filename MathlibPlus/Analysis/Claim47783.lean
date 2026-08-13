import Mathlib

open scoped BigOperators

namespace MathlibPlus.Analysis.Claim47783

/--
Claim 47783 (S4).  The coefficient domain is the positive finite subtype
`↥(Icc 1 n)`, so the definition has no value at `r = 0` or outside the
stated index range.  The harmonic normalization and coefficient formula are
over `ℚ`, making positivity and the exact sum-one assertion literal.
-/
theorem harmonicCoefficients (n : ℕ) (hn : 1 ≤ n) :
    let I : Finset ℕ := Finset.Icc 1 n
    let H : ℚ := ∑ r ∈ I, (r : ℚ)⁻¹
    let a : (↥I) → ℚ := fun r => 1 / ((r.1 : ℚ) * H)
    0 < H ∧
      (∀ r : ↥I, 0 < a r) ∧
      (∑ r ∈ I.attach, a r) = 1 := by
  let I : Finset ℕ := Finset.Icc 1 n
  let H : ℚ := ∑ r ∈ I, (r : ℚ)⁻¹
  let a : (↥I) → ℚ := fun r => 1 / ((r.1 : ℚ) * H)
  have hmem : 1 ∈ I := by simp [I, hn]
  let oneI : ↥I := ⟨1, hmem⟩
  have hterm : (0 : ℚ) < (oneI.1 : ℚ)⁻¹ := by norm_num [oneI]
  have hH : 0 < H := by
    dsimp [H]
    exact lt_of_lt_of_le hterm (Finset.single_le_sum (fun i hi => by
      exact inv_nonneg.mpr (show (0 : ℚ) ≤ (i : ℚ) by positivity)) hmem)
  refine ⟨hH, ?_, ?_⟩
  · intro r
    dsimp [a]
    have hrpos : (0 : ℚ) < (r.1 : ℚ) := by
      have hr1 : 1 ≤ r.1 := (Finset.mem_Icc.mp r.2).1
      exact_mod_cast (Nat.zero_lt_of_lt hr1)
    positivity
  · dsimp [a]
    have hH0 : H ≠ 0 := ne_of_gt hH
    rw [show (∑ r ∈ I.attach, a r) =
        ∑ r ∈ I, 1 / ((r : ℚ) * H) by
      simpa [a] using Finset.sum_attach I
        (fun r => 1 / ((r : ℚ) * H))]
    calc
      (∑ r ∈ I, 1 / ((r : ℚ) * H)) =
          ∑ r ∈ I, (r : ℚ)⁻¹ / H := by
            apply Finset.sum_congr rfl
            intro r hr
            have hr0 : (r : ℚ) ≠ 0 := by
              have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
              exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt hr1))
            field_simp [hH0, hr0]
      _ = (∑ r ∈ I, (r : ℚ)⁻¹) / H := by rw [Finset.sum_div]
      _ = H / H := by rfl
      _ = 1 := by exact div_self hH0

end MathlibPlus.Analysis.Claim47783
