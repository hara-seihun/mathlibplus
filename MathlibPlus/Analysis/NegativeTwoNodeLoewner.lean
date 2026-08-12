import Mathlib

open scoped Matrix

namespace MathlibPlus.Analysis.NegativeTwoNodeLoewner

/-- The displayed rational logarithmic derivative has the claimed negative two-node
Loewner certificate.  The ordinary Loewner matrix uses the derivative on the
confluent diagonal and the first divided difference off the diagonal. -/
theorem negativeTwoNodeLoewnerCertificate :
    let H : ℝ → ℝ := fun x => 4 * (x + 3) / (x ^ 2 + 6 * x + 25)
    let rate : Fin 2 → ℝ := fun i => if i = 0 then 1 / 3 else 1 / 2
    let L : Matrix (Fin 2) (Fin 2) ℝ := fun i j =>
      if i = j then -deriv H (rate i)
      else -(H (rate i) - H (rate j)) / (rate i - rate j)
    L = !![(-99 / 3721 : ℝ), (-156 / 6893 : ℝ);
      (-156 / 6893 : ℝ), (-240 / 12769 : ℝ)] ∧
      L.det = -576 / 47513449 := by
  let H : ℝ → ℝ := fun x => 4 * (x + 3) / (x ^ 2 + 6 * x + 25)
  let rate : Fin 2 → ℝ := fun i => if i = 0 then 1 / 3 else 1 / 2
  let L : Matrix (Fin 2) (Fin 2) ℝ := fun i j =>
    if i = j then -deriv H (rate i)
    else -(H (rate i) - H (rate j)) / (rate i - rate j)
  change L = _ ∧ L.det = _
  have hderiv1 : deriv H (1 / 3 : ℝ) = 99 / 3721 := by
    dsimp [H]
    have hnum : DifferentiableAt ℝ (fun x : ℝ => 4 * (x + 3)) (1 / 3 : ℝ) := by
      fun_prop
    have hden : DifferentiableAt ℝ (fun x : ℝ => x ^ 2 + 6 * x + 25) (1 / 3 : ℝ) := by
      fun_prop
    have h := deriv_div hnum hden
      (by norm_num : (1 / 3 : ℝ) ^ 2 + 6 * (1 / 3) + 25 ≠ 0)
    change deriv ((fun x : ℝ => 4 * (x + 3)) /
      (fun x : ℝ => x ^ 2 + 6 * x + 25)) (1 / 3) = _
    rw [h]
    have hnum' : deriv (fun x : ℝ => 4 * (x + 3)) (1 / 3 : ℝ) = 4 := by
      change deriv ((fun _ : ℝ => 4) * (fun x : ℝ => x + 3)) (1 / 3) = 4
      rw [deriv_mul (by fun_prop) (by fun_prop), deriv_const]
      have hlin : deriv (fun x : ℝ => x + 3) (1 / 3 : ℝ) = 1 := by
        rw [deriv_add_const 3]
        simpa using (deriv_id (1 / 3 : ℝ))
      rw [hlin]
      norm_num
    have hden' : deriv (fun x : ℝ => x ^ 2 + 6 * x + 25) (1 / 3 : ℝ) =
        2 * (1 / 3 : ℝ) + 6 := by
      change deriv ((fun x : ℝ => x ^ 2) + (fun x : ℝ => 6 * x) +
        (fun _ : ℝ => 25)) (1 / 3) = _
      rw [deriv_add (by fun_prop) (by fun_prop), deriv_const]
      rw [deriv_add (by fun_prop) (by fun_prop)]
      have hsq : deriv (fun x : ℝ => x ^ 2) (1 / 3 : ℝ) = 2 * (1 / 3 : ℝ) := by
        change deriv ((id : ℝ → ℝ) ^ 2) (1 / 3) = _
        rw [deriv_pow (by fun_prop) 2]
        rw [deriv_id]
        norm_num [id]
      have hlin6 : deriv (fun x : ℝ => 6 * x) (1 / 3 : ℝ) = 6 := by
        rw [deriv_const_mul 6 (by fun_prop)]
        have hid : deriv (fun x : ℝ => x) (1 / 3 : ℝ) = 1 := by
          simpa using (deriv_id (1 / 3 : ℝ))
        rw [hid]
        norm_num
      rw [hsq, hlin6]
      norm_num
    rw [hnum', hden']
    norm_num
  have hderiv2 : deriv H (1 / 2 : ℝ) = 240 / 12769 := by
    dsimp [H]
    have hnum : DifferentiableAt ℝ (fun x : ℝ => 4 * (x + 3)) (1 / 2 : ℝ) := by
      fun_prop
    have hden : DifferentiableAt ℝ (fun x : ℝ => x ^ 2 + 6 * x + 25) (1 / 2 : ℝ) := by
      fun_prop
    have h := deriv_div hnum hden
      (by norm_num : (1 / 2 : ℝ) ^ 2 + 6 * (1 / 2) + 25 ≠ 0)
    change deriv ((fun x : ℝ => 4 * (x + 3)) /
      (fun x : ℝ => x ^ 2 + 6 * x + 25)) (1 / 2) = _
    rw [h]
    have hnum' : deriv (fun x : ℝ => 4 * (x + 3)) (1 / 2 : ℝ) = 4 := by
      change deriv ((fun _ : ℝ => 4) * (fun x : ℝ => x + 3)) (1 / 2) = 4
      rw [deriv_mul (by fun_prop) (by fun_prop), deriv_const]
      have hlin : deriv (fun x : ℝ => x + 3) (1 / 2 : ℝ) = 1 := by
        rw [deriv_add_const 3]
        simpa using (deriv_id (1 / 2 : ℝ))
      rw [hlin]
      norm_num
    have hden' : deriv (fun x : ℝ => x ^ 2 + 6 * x + 25) (1 / 2 : ℝ) =
        2 * (1 / 2 : ℝ) + 6 := by
      change deriv ((fun x : ℝ => x ^ 2) + (fun x : ℝ => 6 * x) +
        (fun _ : ℝ => 25)) (1 / 2) = _
      rw [deriv_add (by fun_prop) (by fun_prop), deriv_const]
      rw [deriv_add (by fun_prop) (by fun_prop)]
      have hsq : deriv (fun x : ℝ => x ^ 2) (1 / 2 : ℝ) = 2 * (1 / 2 : ℝ) := by
        change deriv ((id : ℝ → ℝ) ^ 2) (1 / 2) = _
        rw [deriv_pow (by fun_prop) 2]
        rw [deriv_id]
        norm_num [id]
      have hlin6 : deriv (fun x : ℝ => 6 * x) (1 / 2 : ℝ) = 6 := by
        rw [deriv_const_mul 6 (by fun_prop)]
        have hid : deriv (fun x : ℝ => x) (1 / 2 : ℝ) = 1 := by
          simpa using (deriv_id (1 / 2 : ℝ))
        rw [hid]
        norm_num
      rw [hsq, hlin6]
      norm_num
    rw [hnum', hden']
    norm_num
  have hval1 : H (1 / 3 : ℝ) = 30 / 61 := by
    dsimp [H]
    norm_num
  have hval2 : H (1 / 2 : ℝ) = 56 / 113 := by
    dsimp [H]
    norm_num
  have hd1 : -deriv H (3⁻¹ : ℝ) = -99 / 3721 := by
    have hi : (3⁻¹ : ℝ) = 1 / 3 := by norm_num
    rw [hi, hderiv1]
    norm_num
  have hd2 : -deriv H (2⁻¹ : ℝ) = -240 / 12769 := by
    have hi : (2⁻¹ : ℝ) = 1 / 2 := by norm_num
    rw [hi, hderiv2]
    norm_num
  have hv1 : H (3⁻¹ : ℝ) = 30 / 61 := by
    have hi : (3⁻¹ : ℝ) = 1 / 3 := by norm_num
    rw [hi, hval1]
  have hv2 : H (2⁻¹ : ℝ) = 56 / 113 := by
    have hi : (2⁻¹ : ℝ) = 1 / 2 := by norm_num
    rw [hi, hval2]
  have hL : L = !![(-99 / 3721 : ℝ), (-156 / 6893 : ℝ);
      (-156 / 6893 : ℝ), (-240 / 12769 : ℝ)] := by
    ext i j
    fin_cases i <;> fin_cases j
    · simp [L, rate]
      exact hd1
    · simp [L, rate]
      rw [hv1, hv2]
      norm_num
    · simp [L, rate]
      rw [hv1, hv2]
      norm_num
    · simp [L, rate]
      exact hd2
  constructor
  · exact hL
  · rw [hL, Matrix.det_fin_two]
    norm_num

end MathlibPlus.Analysis.NegativeTwoNodeLoewner
