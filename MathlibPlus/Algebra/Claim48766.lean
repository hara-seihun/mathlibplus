import Mathlib

namespace MathlibPlus.Algebra.Claim48766

noncomputable section

open MvPolynomial

abbrev PowerSumPolynomial := MvPolynomial ℕ ℤ

/-- The variable `p_n` in the power-sum polynomial carrier. -/
noncomputable def p (n : ℕ) : PowerSumPolynomial := X n

def p522 : PowerSumPolynomial := p 5 * p 2 ^ 2
def p441 : PowerSumPolynomial := p 4 ^ 2 * p 1
def p333 : PowerSumPolynomial := p 3 ^ 3
def p531 : PowerSumPolynomial := p 5 * p 3 * p 1
def p432 : PowerSumPolynomial := p 4 * p 3 * p 2

/-- The degree-nine kernel vector displayed in claim 48766. -/
noncomputable def K9 : PowerSumPolynomial :=
  p522 + p441 + p333 - p531 - 2 * p432

/-- The displayed vector is homogeneous for the usual power-sum weight. -/
theorem K9_isWeightedHomogeneous_claim48766 :
    IsWeightedHomogeneous (fun i : ℕ => i) K9 9 := by
  have h1 : IsWeightedHomogeneous (fun i : ℕ => i) (p 1) 1 := by
    simpa [p] using (isWeightedHomogeneous_X (R := ℤ) (fun i : ℕ => i) 1)
  have h2 : IsWeightedHomogeneous (fun i : ℕ => i) (p 2) 2 := by
    simpa [p] using (isWeightedHomogeneous_X (R := ℤ) (fun i : ℕ => i) 2)
  have h3 : IsWeightedHomogeneous (fun i : ℕ => i) (p 3) 3 := by
    simpa [p] using (isWeightedHomogeneous_X (R := ℤ) (fun i : ℕ => i) 3)
  have h4 : IsWeightedHomogeneous (fun i : ℕ => i) (p 4) 4 := by
    simpa [p] using (isWeightedHomogeneous_X (R := ℤ) (fun i : ℕ => i) 4)
  have h5 : IsWeightedHomogeneous (fun i : ℕ => i) (p 5) 5 := by
    simpa [p] using (isWeightedHomogeneous_X (R := ℤ) (fun i : ℕ => i) 5)
  have h522 : IsWeightedHomogeneous (fun i : ℕ => i) p522 9 := by
    simpa [p522] using h5.mul (h2.pow 2)
  have h441 : IsWeightedHomogeneous (fun i : ℕ => i) p441 9 := by
    simpa [p441] using (h4.pow 2).mul h1
  have h333 : IsWeightedHomogeneous (fun i : ℕ => i) p333 9 := by
    simpa [p333] using h3.pow 3
  have h531 : IsWeightedHomogeneous (fun i : ℕ => i) p531 9 := by
    simpa [p531, mul_assoc] using h5.mul (h3.mul h1)
  have h432 : IsWeightedHomogeneous (fun i : ℕ => i) p432 9 := by
    simpa [p432, mul_assoc] using h4.mul (h3.mul h2)
  have h2p432 : IsWeightedHomogeneous (fun i : ℕ => i) (2 * p432) 9 := by
    simpa using h432.C_mul 2
  dsimp [K9]
  exact (((h522.add h441).add h333).sub h531).sub h2p432

/-- The derivative of a natural scalar is zero in this polynomial carrier. -/
lemma pderiv_two_scalar (i : ℕ) :
    pderiv i (2 : PowerSumPolynomial) = 0 := by
  have h : (2 : PowerSumPolynomial) = 1 + 1 := by norm_num
  rw [h]
  simp

/-- The five displayed partial derivatives of `K9`. -/
theorem pderiv_one_claim48768 :
    pderiv 1 K9 = p 4 ^ 2 - p 5 * p 3 := by
  classical
  simp [K9, p522, p441, p333, p531, p432, p,
    MvPolynomial.pderiv_C, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_pow,
    pderiv_two_scalar, mul_assoc, mul_left_comm, mul_comm] <;> ring

theorem pderiv_two_claim48768 :
    pderiv 2 K9 = 2 * (p 5 * p 2 - p 4 * p 3) := by
  classical
  simp [K9, p522, p441, p333, p531, p432, p,
    MvPolynomial.pderiv_C, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_pow,
    pderiv_two_scalar, mul_assoc, mul_left_comm, mul_comm] <;> ring

theorem pderiv_three_claim48768 :
    pderiv 3 K9 = 3 * p 3 ^ 2 - p 5 * p 1 - 2 * (p 4 * p 2) := by
  classical
  simp [K9, p522, p441, p333, p531, p432, p,
    MvPolynomial.pderiv_C, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_pow,
    pderiv_two_scalar, mul_assoc, mul_left_comm, mul_comm]

theorem pderiv_four_claim48768 :
    pderiv 4 K9 = 2 * (p 4 * p 1 - p 3 * p 2) := by
  classical
  simp [K9, p522, p441, p333, p531, p432, p,
    MvPolynomial.pderiv_C, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_pow,
    pderiv_two_scalar, mul_assoc, mul_left_comm, mul_comm] <;> ring

theorem pderiv_five_claim48768 :
    pderiv 5 K9 = p 2 ^ 2 - p 3 * p 1 := by
  classical
  simp [K9, p522, p441, p333, p531, p432, p,
    MvPolynomial.pderiv_C, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_pow,
    pderiv_two_scalar, mul_assoc, mul_left_comm, mul_comm] <;> ring

/-- No power-sum variable of index at least six occurs in `K9`. -/
theorem pderiv_ge_six_claim48770 (k : ℕ) (hk : 6 ≤ k) :
    pderiv k K9 = 0 := by
  classical
  have hk1 : k ≠ 1 := by omega
  have hk2 : k ≠ 2 := by omega
  have hk3 : k ≠ 3 := by omega
  have hk4 : k ≠ 4 := by omega
  have hk5 : k ≠ 5 := by omega
  have hk1' : 1 ≠ k := Ne.symm hk1
  have hk2' : 2 ≠ k := Ne.symm hk2
  have hk3' : 3 ≠ k := Ne.symm hk3
  have hk4' : 4 ≠ k := Ne.symm hk4
  have hk5' : 5 ≠ k := Ne.symm hk5
  simp [K9, p522, p441, p333, p531, p432, p,
    MvPolynomial.pderiv_C, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_pow,
    pderiv_two_scalar, hk1, hk2, hk3, hk4, hk5, hk1', hk2', hk3', hk4', hk5'] <;> ring

/-- The degree-nine derivative certificates are all nonzero in the polynomial carrier. -/
theorem pderiv_one_ne_zero_claim48768 : pderiv 1 K9 ≠ 0 := by
  rw [pderiv_one_claim48768]
  intro h
  have he := congrArg (eval (fun n : ℕ => if n = 4 then (1 : ℤ) else 0)) h
  norm_num [p] at he

theorem pderiv_two_ne_zero_claim48768 : pderiv 2 K9 ≠ 0 := by
  rw [pderiv_two_claim48768]
  intro h
  have he := congrArg
    (eval (fun n : ℕ => if n = 5 then (1 : ℤ) else if n = 2 then 1 else 0)) h
  norm_num [p] at he

theorem pderiv_three_ne_zero_claim48768 : pderiv 3 K9 ≠ 0 := by
  rw [pderiv_three_claim48768]
  intro h
  have he := congrArg (eval (fun n : ℕ => if n = 3 then (1 : ℤ) else 0)) h
  norm_num [p] at he

theorem pderiv_four_ne_zero_claim48768 : pderiv 4 K9 ≠ 0 := by
  rw [pderiv_four_claim48768]
  intro h
  have he := congrArg
    (eval (fun n : ℕ => if n = 4 then (1 : ℤ) else if n = 1 then 1 else 0)) h
  norm_num [p] at he

theorem pderiv_five_ne_zero_claim48768 : pderiv 5 K9 ≠ 0 := by
  rw [pderiv_five_claim48768]
  intro h
  have he := congrArg (eval (fun n : ℕ => if n = 2 then (1 : ℤ) else 0)) h
  norm_num [p] at he

/-- The two compressed partition terms in the source retain their `p₁` factors. -/
theorem p_one_dvd_p441_claim48774 : p 1 ∣ p441 := by
  refine ⟨p 4 ^ 2, ?_⟩
  dsimp [p441]
  ring

theorem p_one_dvd_p531_claim48774 : p 1 ∣ p531 := by
  refine ⟨p 5 * p 3, ?_⟩
  dsimp [p531]
  ring

end

end MathlibPlus.Algebra.Claim48766
