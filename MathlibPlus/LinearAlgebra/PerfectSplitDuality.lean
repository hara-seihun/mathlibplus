import Mathlib

namespace MathlibPlus.LinearAlgebra

/-- Claim 12952: the diagonal map with factors `2` and `1/2` preserves the
split form, while its invariant symmetric forms have zero diagonal and no
positive-definite conformal form exists. -/
theorem perfectSplitDualityNoPositivity_claim12952 :
    let U : Matrix (Fin 2) (Fin 2) ℝ := !![2, 0; 0, (1 / 2 : ℝ)]
    let J : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]
    U.transpose * J * U = J ∧
      (∀ S : Matrix (Fin 2) (Fin 2) ℝ,
        S.IsSymm → U.transpose * S * U = S →
          S 0 0 = 0 ∧ S 1 1 = 0) ∧
      (∀ (S : Matrix (Fin 2) (Fin 2) ℝ) (c : ℝ),
        S.PosDef → U.transpose * S * U = c • S → c = 4 ∧ c = 1 / 4) ∧
      (¬ ∃ (S : Matrix (Fin 2) (Fin 2) ℝ) (c : ℝ),
        S.PosDef ∧ U.transpose * S * U = c • S) := by
  dsimp
  let U : Matrix (Fin 2) (Fin 2) ℝ := !![2, 0; 0, (1 / 2 : ℝ)]
  let J : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]
  have hUJ : U.transpose * J * U = J := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [U, J, Matrix.mul_apply, Fin.sum_univ_succ]
  have hinv : ∀ S : Matrix (Fin 2) (Fin 2) ℝ,
      S.IsSymm → U.transpose * S * U = S →
        S 0 0 = 0 ∧ S 1 1 = 0 := by
    intro S _ hS
    have h00 := congr_fun (congr_fun hS 0) 0
    have h11 := congr_fun (congr_fun hS 1) 1
    simp [U, Matrix.mul_apply, Fin.sum_univ_succ] at h00 h11
    constructor <;> nlinarith
  have hconf : ∀ (S : Matrix (Fin 2) (Fin 2) ℝ) (c : ℝ),
      S.PosDef → U.transpose * S * U = c • S → c = 4 ∧ c = 1 / 4 := by
    intro S c hS hcon
    have h00 := congr_fun (congr_fun hcon 0) 0
    have h11 := congr_fun (congr_fun hcon 1) 1
    have hx0 : (fun i : Fin 2 => if i = 0 then (1 : ℝ) else 0) ≠ 0 := by
      intro h
      have h' := congr_fun h 0
      norm_num at h'
    have hx1 : (fun i : Fin 2 => if i = 1 then (1 : ℝ) else 0) ≠ 0 := by
      intro h
      have h' := congr_fun h 1
      norm_num at h'
    have h00pos : 0 < S 0 0 := by
      have h := hS.re_dotProduct_pos
        (x := fun i : Fin 2 => if i = 0 then 1 else 0) hx0
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] using h
    have h11pos : 0 < S 1 1 := by
      have h := hS.re_dotProduct_pos
        (x := fun i : Fin 2 => if i = 1 then 1 else 0) hx1
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] using h
    simp [U, Matrix.mul_apply, Fin.sum_univ_succ] at h00 h11
    constructor <;> nlinarith
  have hno : ¬ ∃ (S : Matrix (Fin 2) (Fin 2) ℝ) (c : ℝ),
      S.PosDef ∧ U.transpose * S * U = c • S := by
    rintro ⟨S, c, hS, hcon⟩
    obtain ⟨hc4, hcquarter⟩ := hconf S c hS hcon
    norm_num [hc4] at hcquarter
  exact ⟨hUJ, hinv, hconf, hno⟩

end MathlibPlus.LinearAlgebra
