import Mathlib

noncomputable section

namespace MathlibPlus.Analysis.PoleAmplitude

/-- The multiplier applied to the amplitude at `γ j²` when `γ m²` is deleted. -/
def deletionMultiplier {N : ℕ} (γ : Fin N → ℝ) (m j : Fin N) : ℝ :=
  1 - γ j ^ 2 / γ m ^ 2

/-- The alternating-sign condition for a finite indexed sequence. -/
def Alternates {N : ℕ} (c : Fin N → ℝ) : Prop :=
  ∀ ⦃i j : Fin N⦄, i.val + 1 = j.val → c i * c j < 0

/-- The surviving amplitude sequence after deleting index `m` and reindexing. -/
def deletedAmplitudes {n : ℕ} (γ c : Fin (n + 1) → ℝ) (m : Fin (n + 1)) : Fin n → ℝ :=
  fun j => deletionMultiplier γ m (m.succAbove j) * c (m.succAbove j)

private lemma same_sign_of_two_neg_products {a b d : ℝ}
    (hab : a * b < 0) (hbd : b * d < 0) : 0 < a * d := by
  rcases (mul_neg_iff.mp hab) with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · rcases (mul_neg_iff.mp hbd) with ⟨hb', hd⟩ | ⟨hb', hd⟩
    · exact (not_lt_of_ge (le_of_lt hb') hb).elim
    · exact mul_pos ha hd
  · rcases (mul_neg_iff.mp hbd) with ⟨hb', hd⟩ | ⟨hb', hd⟩
    · exact mul_pos_of_neg_of_neg ha hd
    · exact (not_lt_of_ge (le_of_lt hb) hb').elim

/-- Ordered positive pole nodes and alternating original amplitudes retain the
alternating sign pattern after one pole is deleted. -/
theorem transformedPoleAmplitudes_preserveAlternation
    {n : ℕ} (γ c : Fin (n + 1) → ℝ)
    (hγpos : ∀ j, 0 < γ j)
    (hγmono : StrictMono γ)
    (hc : Alternates c) (m : Fin (n + 1)) :
    (∀ j, j < m → 0 < deletionMultiplier γ m j) ∧
      (∀ j, m < j → deletionMultiplier γ m j < 0) ∧
      Alternates (deletedAmplitudes γ c m) := by
  have hmul_pos : ∀ {j : Fin (n + 1)}, j < m → 0 < deletionMultiplier γ m j := by
    intro j hj
    have hsq : γ j ^ 2 < γ m ^ 2 := by
      have hlt : γ j < γ m := hγmono hj
      nlinarith [hγpos j, hγpos m]
    have hden : 0 < γ m ^ 2 := sq_pos_of_pos (hγpos m)
    unfold deletionMultiplier
    have hquot : γ j ^ 2 / γ m ^ 2 < 1 := by
      apply (div_lt_iff₀ hden).2
      simpa using hsq
    linarith
  have hmul_neg : ∀ {j : Fin (n + 1)}, m < j → deletionMultiplier γ m j < 0 := by
    intro j hj
    have hsq : γ m ^ 2 < γ j ^ 2 := by
      have hlt : γ m < γ j := hγmono hj
      nlinarith [hγpos j, hγpos m]
    have hden : 0 < γ m ^ 2 := sq_pos_of_pos (hγpos m)
    unfold deletionMultiplier
    have hquot : 1 < γ j ^ 2 / γ m ^ 2 := by
      apply (lt_div_iff₀ hden).2
      simpa using hsq
    linarith
  refine ⟨?_, ?_, ?_⟩
  · intro j hj
    exact hmul_pos hj
  · intro j hj
    exact hmul_neg hj
  · intro i j hij
    by_cases hafter : m ≤ i.castSucc
    · have hafterj : m ≤ j.castSucc := by
        apply Fin.le_iff_val_le_val.mpr
        change m.val ≤ j.val
        have hafter' : m.val ≤ i.val := by
          exact Fin.le_iff_val_le_val.mp hafter
        omega
      have hmi : m.succAbove i = i.succ := Fin.succAbove_of_le_castSucc m i hafter
      have hmj : m.succAbove j = j.succ := Fin.succAbove_of_le_castSucc m j hafterj
      simp only [deletedAmplitudes, hmi, hmj]
      have hmi' : m < i.succ := lt_of_le_of_lt hafter i.castSucc_lt_succ
      have hmj' : m < j.succ := lt_of_le_of_lt hafterj j.castSucc_lt_succ
      have hij' : i.succ.val + 1 = j.succ.val := by
        change i.val + 1 + 1 = j.val + 1
        omega
      have hmult : 0 < deletionMultiplier γ m i.succ *
          deletionMultiplier γ m j.succ :=
        mul_pos_of_neg_of_neg (hmul_neg hmi') (hmul_neg hmj')
      calc
        (deletionMultiplier γ m i.succ * c i.succ) *
            (deletionMultiplier γ m j.succ * c j.succ) =
            (deletionMultiplier γ m i.succ * deletionMultiplier γ m j.succ) *
              (c i.succ * c j.succ) := by ring
        _ < 0 := mul_neg_of_pos_of_neg hmult (hc hij')
    · have hbefore : i.castSucc < m := lt_of_not_ge hafter
      by_cases hbeforej : j.castSucc < m
      · have hmi : m.succAbove i = i.castSucc :=
          Fin.succAbove_of_castSucc_lt m i hbefore
        have hmj : m.succAbove j = j.castSucc :=
          Fin.succAbove_of_castSucc_lt m j hbeforej
        simp only [deletedAmplitudes, hmi, hmj]
        have hmi' : i.castSucc < m := hbefore
        have hmj' : j.castSucc < m := hbeforej
        have hij' : i.castSucc.val + 1 = j.castSucc.val := by
          simpa [Fin.val_castSucc] using hij
        have hmult : 0 < deletionMultiplier γ m i.castSucc *
            deletionMultiplier γ m j.castSucc :=
          mul_pos (hmul_pos hmi') (hmul_pos hmj')
        calc
          (deletionMultiplier γ m i.castSucc * c i.castSucc) *
              (deletionMultiplier γ m j.castSucc * c j.castSucc) =
              (deletionMultiplier γ m i.castSucc * deletionMultiplier γ m j.castSucc) *
                (c i.castSucc * c j.castSucc) := by ring
          _ < 0 := mul_neg_of_pos_of_neg hmult (hc hij')
      · have hnotbeforej' : m.val ≤ j.val := by
          apply Nat.le_of_not_gt
          intro h
          apply hbeforej
          apply Fin.lt_iff_val_lt_val.mpr
          simpa [Fin.val_castSucc] using h
        have hafterj : m ≤ j.castSucc := by
          apply Fin.le_iff_val_le_val.mpr
          change m.val ≤ j.val
          exact hnotbeforej'
        have hmi : m.succAbove i = i.castSucc :=
          Fin.succAbove_of_castSucc_lt m i hbefore
        have hmj : m.succAbove j = j.succ :=
          Fin.succAbove_of_le_castSucc m j hafterj
        simp only [deletedAmplitudes, hmi, hmj]
        have hbefore' : i.val < m.val := by
          exact Fin.lt_iff_val_lt_val.mp hbefore
        have hcm' : i.val + 1 = m.val := by
          omega
        have hmjval' : m.val + 1 = j.val + 1 := by
          omega
        have hcm : i.castSucc.val + 1 = m.val := by
          simpa [Fin.val_castSucc] using hcm'
        have hmjval : m.val + 1 = j.succ.val := by
          simpa [Fin.val_succ] using hmjval'
        have hleft : c i.castSucc * c m < 0 := hc hcm
        have hright : c m * c j.succ < 0 := hc hmjval
        have hsame : 0 < c i.castSucc * c j.succ :=
          same_sign_of_two_neg_products hleft hright
        have hmulleft : 0 < deletionMultiplier γ m i.castSucc := hmul_pos hbefore
        have hmulright : deletionMultiplier γ m j.succ < 0 := hmul_neg
          (lt_of_le_of_lt hafterj j.castSucc_lt_succ)
        have hmult : deletionMultiplier γ m i.castSucc *
            deletionMultiplier γ m j.succ < 0 :=
          mul_neg_of_pos_of_neg hmulleft hmulright
        calc
          (deletionMultiplier γ m i.castSucc * c i.castSucc) *
              (deletionMultiplier γ m j.succ * c j.succ) =
              (deletionMultiplier γ m i.castSucc * deletionMultiplier γ m j.succ) *
                (c i.castSucc * c j.succ) := by ring
          _ < 0 := mul_neg_of_neg_of_pos hmult hsame

end MathlibPlus.Analysis.PoleAmplitude
