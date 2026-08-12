import Mathlib.Tactic

namespace MathlibPlus.Analysis

/-!
Claim 18591: the displayed cubic has a unique real zero.  The decimal in the
source is an approximation, so it is represented by the exact rational
interval given by the displayed digits.
-/

/-- The cubic wall polynomial has one real zero, with the stated decimal
approximation. -/
theorem cubicWallRoot_claim18591 :
    let C : ℝ → ℝ := fun q => 64 * q ^ 3 - 432 * q ^ 2 + 924 * q - 693
    ∃ qstar : ℝ,
      C qstar = 0 ∧
        (3.52707460930038659024091016827 : ℝ) < qstar ∧
          qstar < 3.52707460930038659024091016829 ∧
            ∀ q : ℝ, C q = 0 → q = qstar := by
  dsimp
  let C : ℝ → ℝ := fun q => 64 * q ^ 3 - 432 * q ^ 2 + 924 * q - 693
  have hneg : ∀ x : ℝ, x ≤ (11 / 4 : ℝ) → C x < 0 := by
    intro x hx
    let y : ℝ := x - 7 / 4
    have hform : C x = 64 * y ^ 3 - 96 * y ^ 2 - 56 := by
      dsimp [C, y]
      ring
    by_cases hy : y ≤ 0
    · have hy3 : y ^ 3 ≤ 0 := by
        have hmul : y * y ^ 2 ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg hy (sq_nonneg y)
        nlinarith
      nlinarith [hform, sq_nonneg y]
    · have hy0 : 0 ≤ y := le_of_not_ge hy
      have hy1 : y ≤ 1 := by
        dsimp [y]
        linarith
      have hdiff : y ^ 3 - y ^ 2 ≤ 0 := by
        have hmul : y ^ 2 * (y - 1) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (sq_nonneg y) (by linarith)
        nlinarith
      nlinarith [hform, sq_nonneg y]
  have hcont : ContinuousOn C (Set.Icc (11 / 4 : ℝ) 4) := by
    fun_prop
  have hleft : C (11 / 4 : ℝ) < 0 := by
    norm_num [C]
  have hright : 0 < C 4 := by
    norm_num [C]
  have hzero_mem : (0 : ℝ) ∈ Set.Icc (C (11 / 4 : ℝ)) (C 4) :=
    ⟨le_of_lt hleft, le_of_lt hright⟩
  rcases intermediate_value_Icc (by norm_num : (11 / 4 : ℝ) ≤ 4) hcont hzero_mem with
    ⟨qstar, hqmem, hqzero⟩
  have hqzero' : C qstar = 0 := hqzero
  have hqgt : (11 / 4 : ℝ) < qstar := by
    by_contra h
    exact (ne_of_lt (hneg qstar (le_of_not_gt h))) hqzero'
  have hcont_interval :
      ContinuousOn C
        (Set.Icc (3.52707460930038659024091016827 : ℝ)
          3.52707460930038659024091016829) := by
    fun_prop
  have hlow : C (3.52707460930038659024091016827 : ℝ) < 0 := by
    norm_num [C]
  have hupp : 0 < C (3.52707460930038659024091016829 : ℝ) := by
    norm_num [C]
  have hinterval_mem :
      (0 : ℝ) ∈ Set.Icc
        (C (3.52707460930038659024091016827 : ℝ))
        (C 3.52707460930038659024091016829) :=
    ⟨le_of_lt hlow, le_of_lt hupp⟩
  rcases intermediate_value_Icc
      (by norm_num :
        (3.52707460930038659024091016827 : ℝ) ≤
          3.52707460930038659024091016829)
      hcont_interval hinterval_mem with
    ⟨qinterval, hqinterval, hqinterval_zero⟩
  have hqinterval_zero' : C qinterval = 0 := hqinterval_zero
  have hqinterval_eq : qinterval = qstar := by
    exact (by
      have := hqzero'
      have := hqinterval_zero'
      have hqinterval_gt : (11 / 4 : ℝ) < qinterval := by
        by_contra h
        exact (ne_of_lt (hneg qinterval (le_of_not_gt h))) hqinterval_zero'
      let u : ℝ := qinterval - 11 / 4
      let v : ℝ := qstar - 11 / 4
      have hu : 0 < u := by dsimp [u]; linarith
      have hv : 0 < v := by dsimp [v]; linarith
      have hfactor :
          (qinterval - qstar) *
              (64 * u ^ 2 + 64 * u * v + 64 * v ^ 2 + 96 * (u + v)) = 0 := by
        calc
          (qinterval - qstar) *
                (64 * u ^ 2 + 64 * u * v + 64 * v ^ 2 + 96 * (u + v)) =
              C qinterval - C qstar := by
                dsimp [C, u, v]
                ring
          _ = 0 := by rw [hqinterval_zero', hqzero']; ring
      have hpositive :
          0 < 64 * u ^ 2 + 64 * u * v + 64 * v ^ 2 + 96 * (u + v) := by
        positivity
      rcases mul_eq_zero.mp hfactor with hdiff | hpositive_zero
      · linarith
      · linarith
    )
  refine ⟨qstar, hqzero', ?_, ?_, ?_⟩
  · have hleft_ne :
        (3.52707460930038659024091016827 : ℝ) ≠ qinterval := by
      intro heq
      rw [← heq] at hqinterval_zero'
      linarith
    have hstrict := lt_of_le_of_ne hqinterval.1 hleft_ne
    simpa [hqinterval_eq] using hstrict
  · have hright_ne :
        qinterval ≠ (3.52707460930038659024091016829 : ℝ) := by
      intro heq
      rw [heq] at hqinterval_zero'
      linarith
    have hstrict := lt_of_le_of_ne hqinterval.2 hright_ne
    simpa [hqinterval_eq] using hstrict
  · intro q hq
    change C q = 0 at hq
    have hqgt' : (11 / 4 : ℝ) < q := by
      by_contra h
      exact (ne_of_lt (hneg q (le_of_not_gt h))) hq
    let u : ℝ := q - 11 / 4
    let v : ℝ := qstar - 11 / 4
    have hu : 0 < u := by dsimp [u]; linarith
    have hv : 0 < v := by dsimp [v]; linarith
    have hfactor :
        (q - qstar) *
            (64 * u ^ 2 + 64 * u * v + 64 * v ^ 2 + 96 * (u + v)) = 0 := by
      calc
        (q - qstar) *
              (64 * u ^ 2 + 64 * u * v + 64 * v ^ 2 + 96 * (u + v)) =
            C q - C qstar := by
              dsimp [C, u, v]
              ring
        _ = 0 := by rw [hq, hqzero']; ring
    have hpositive :
        0 < 64 * u ^ 2 + 64 * u * v + 64 * v ^ 2 + 96 * (u + v) := by
      positivity
    rcases mul_eq_zero.mp hfactor with hdiff | hpositive_zero
    · linarith
    · linarith

end MathlibPlus.Analysis
