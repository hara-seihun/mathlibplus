import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace MathlibPlus.Analysis.Claim12879

/-- Claim 12879: the support function `q log r - r` on the positive axis
has supremum `q log q - q`, attained uniquely at `r = q`. -/
theorem axisSupportBarrier (q : ℝ) (hq : 0 < q) :
    let f : ℝ → ℝ := fun r => q * Real.log r - r
    let S : Set ℝ := f '' Set.Ioi 0
    let v : ℝ := f q
    sSup S = v ∧
      (∀ r : ℝ, 0 < r → f r ≤ v) ∧
      (∀ r : ℝ, 0 < r → (f r = v ↔ r = q)) := by
  dsimp
  let f : ℝ → ℝ := fun r => q * Real.log r - r
  let S : Set ℝ := f '' Set.Ioi 0
  let v : ℝ := f q
  have hbound : ∀ r : ℝ, 0 < r → f r ≤ v := by
    intro r hr
    have hratio : 0 < r / q := div_pos hr hq
    have hlog : Real.log (r / q) ≤ r / q - 1 :=
      Real.log_le_sub_one_of_pos hratio
    rw [Real.log_div (ne_of_gt hr) (ne_of_gt hq)] at hlog
    have hscaled := mul_le_mul_of_nonneg_left hlog hq.le
    have hqdiv : q * (r / q) = r := by
      field_simp
    dsimp [f, v]
    nlinarith [hscaled, hqdiv]
  have heq : ∀ r : ℝ, 0 < r → (f r = v ↔ r = q) := by
    intro r hr
    constructor
    · intro h
      by_contra hne
      have hratio : 0 < r / q := div_pos hr hq
      have hratio_ne : r / q ≠ 1 := by
        intro hratio_one
        apply hne
        field_simp at hratio_one
        exact hratio_one
      have hlog : Real.log (r / q) < r / q - 1 :=
        Real.log_lt_sub_one_of_pos hratio hratio_ne
      rw [Real.log_div (ne_of_gt hr) (ne_of_gt hq)] at hlog
      have hscaled := mul_lt_mul_of_pos_left hlog hq
      have hqdiv : q * (r / q) = r := by
        field_simp
      dsimp [f, v] at h
      nlinarith [hscaled, hqdiv]
    · rintro rfl
      rfl
  have hmem : v ∈ S := by
    refine ⟨q, Set.mem_Ioi.mpr hq, ?_⟩
    rfl
  have hSnonempty : S.Nonempty := ⟨v, hmem⟩
  have hSup : sSup S = v := by
    apply csSup_eq_of_forall_le_of_forall_lt_exists_gt hSnonempty
    · rintro x ⟨r, hr, rfl⟩
      exact hbound r hr
    · intro w hw
      exact ⟨v, hmem, hw⟩
  exact ⟨hSup, hbound, heq⟩

end MathlibPlus.Analysis.Claim12879
