import Mathlib

noncomputable section

namespace MathlibPlus.Analysis.Claim57694

/-- The reciprocal scale in the finite central perturbation of the unit lattice. -/
def epsilon (m : ℕ) : ℝ := (m : ℝ)⁻¹

/-- The bi-infinite gap sequence from claim 57694. -/
def gap (m : ℕ) (i : ℤ) : ℝ :=
  if i = 0 then 1
  else if i = 1 ∨ i = (-1 : ℤ) then epsilon m
  else if i = 2 ∨ i = (-2 : ℤ) then (epsilon m) ^ 3
  else 1

/-- The cumulative positions, written explicitly so that the two-sided recurrence
is a theorem rather than an additional hidden choice of sequence. -/
def position (m : ℕ) (i : ℤ) : ℝ :=
  if i = 0 then 0
  else if i = 1 then 1
  else if i = 2 then 1 + epsilon m
  else if 3 ≤ i then (i : ℝ) - 2 + (epsilon m + (epsilon m) ^ 3)
  else if i = (-1 : ℤ) then -epsilon m
  else if i = (-2 : ℤ) then -(epsilon m + (epsilon m) ^ 3)
  else (i : ℝ) + 2 - (epsilon m + (epsilon m) ^ 3)

lemma epsilon_pos {m : ℕ} (hm : 3 ≤ m) : 0 < epsilon m := by
  have hm' : (0 : ℝ) < (m : ℝ) := by
    exact_mod_cast (Nat.zero_lt_of_lt hm)
  dsimp [epsilon]
  positivity

lemma gap_pos {m : ℕ} (hm : 3 ≤ m) (i : ℤ) : 0 < gap m i := by
  have he : 0 < epsilon m := epsilon_pos hm
  by_cases h0 : i = 0
  · simp [gap, h0]
  by_cases h1 : i = 1 ∨ i = (-1 : ℤ)
  · simp [gap, h0, h1, he]
  by_cases h2 : i = 2 ∨ i = (-2 : ℤ)
  · simp [gap, h0, h1, h2, he]
  · simp [gap, h0, h1, h2]

lemma position_zero (m : ℕ) : position m 0 = 0 := by
  simp [position]

lemma position_succ_eq {m : ℕ} (hm : 3 ≤ m) (i : ℤ) :
    position m (i + 1) = position m i + gap m i := by
  have he : 0 < epsilon m := epsilon_pos hm
  have he3 : 0 < (epsilon m) ^ 3 := by positivity
  have hdelta : epsilon m + (epsilon m) ^ 3 =
      (epsilon m + (epsilon m) ^ 3) := rfl
  by_cases h0 : i = 0
  · subst i
    simp [position, gap]
  by_cases h1 : i = 1
  · subst i
    simp [position, gap]
  by_cases h2 : i = 2
  · subst i
    simp [position, gap]
    ring
  by_cases hm1 : i = (-1 : ℤ)
  · subst i
    simp [position, gap]
  by_cases hm2 : i = (-2 : ℤ)
  · subst i
    simp [position, gap]
  by_cases hge : 3 ≤ i
  · have hge' : 3 ≤ i + 1 := by omega
    have hn0' : i + 1 ≠ 0 := by omega
    have hn2' : i + 1 ≠ 2 := by omega
    simp [position, gap, h0, h1, h2, hm1, hm2, hge, hge', hn0', hn2']
    ring
  · have hle : i ≤ (-3 : ℤ) := by omega
    by_cases hm3 : i = (-3 : ℤ)
    · subst i
      simp [position, gap, h0, h1, h2, hm1, hm2]
      ring
    · have hle4 : i ≤ (-4 : ℤ) := by omega
      have hle3' : i + 1 ≤ (-3 : ℤ) := by omega
      have hge' : ¬ (3 ≤ i + 1) := by omega
      have hn0' : i + 1 ≠ 0 := by omega
      have hn1' : i + 1 ≠ 1 := by omega
      have hn2' : i + 1 ≠ 2 := by omega
      have hnm1' : i + 1 ≠ (-1 : ℤ) := by omega
      have hnm2' : i + 1 ≠ (-2 : ℤ) := by omega
      simp [position, gap, h0, h1, h2, hm1, hm2, hge,
        hge', hn0', hn1', hn2', hnm1', hnm2']
      ring

lemma position_right_tail {m : ℕ} (i : ℤ) (hi : 3 ≤ i) :
    position m i = (i : ℝ) - 2 + (epsilon m + (epsilon m) ^ 3) := by
  have h0 : i ≠ 0 := by omega
  have h1 : i ≠ 1 := by omega
  have h2 : i ≠ 2 := by omega
  simp [position, h0, h1, h2, hi]

lemma position_left_tail {m : ℕ} (i : ℤ) (hi : i ≤ (-2 : ℤ)) :
    position m i = (i : ℝ) + 2 - (epsilon m + (epsilon m) ^ 3) := by
  have h0 : i ≠ 0 := by omega
  have h1 : i ≠ 1 := by omega
  have h2 : i ≠ 2 := by omega
  have hge : ¬ (3 ≤ i) := by omega
  by_cases hm2 : i = (-2 : ℤ)
  · subst i
    norm_num [position]
  · have hm1 : i ≠ (-1 : ℤ) := by omega
    simp [position, h0, h1, h2, hge, hm1, hm2]

/-- Precise formalization of the explicit part of claim 57694.  The final
"bounded counting discrepancy" sentence is represented by its exact content:
outside the finite central window both tails have unit gaps and the displayed
unit-lattice affine formulas. -/
def gapSequenceClaim : Prop :=
  ∀ m : ℕ, 3 ≤ m →
    (∀ i : ℤ, 0 < gap m i) ∧
    position m 0 = 0 ∧
    (∀ i : ℤ, position m (i + 1) = position m i + gap m i) ∧
    (∀ i : ℤ, 3 ≤ i →
      position m i = (i : ℝ) - 2 + (epsilon m + (epsilon m) ^ 3)) ∧
    (∀ i : ℤ, i ≤ (-2 : ℤ) →
      position m i = (i : ℝ) + 2 - (epsilon m + (epsilon m) ^ 3))

theorem gapSequenceClaim_proved : gapSequenceClaim := by
  intro m hm
  refine ⟨gap_pos hm, position_zero m, ?_, ?_, ?_⟩
  · intro i
    exact position_succ_eq hm i
  · intro i hi
    exact position_right_tail i hi
  · intro i hi
    exact position_left_tail i hi

end MathlibPlus.Analysis.Claim57694
