import Mathlib

namespace MathlibPlus.Analysis

/-- Exact five-factor product specialization of the order-six signed
Karlin determinant.  The five positive parameters are the source's
positive reciprocal roots; `G` and `D₆` are kept theorem-local so this
statement introduces no source-free auxiliary definitions. -/
theorem exactFivePositiveRootFormula_claim892
    (a b c d e : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e) :
    let G : Polynomial ℝ :=
      (Polynomial.C a * Polynomial.X + 1) *
      (Polynomial.C b * Polynomial.X + 1) *
      (Polynomial.C c * Polynomial.X + 1) *
      (Polynomial.C d * Polynomial.X + 1) *
      (Polynomial.C e * Polynomial.X + 1)
    let D₆ : ℝ := Matrix.det (fun i j : Fin 6 =>
      ((Polynomial.derivative^[5 + j.1 - i.1]) G).eval 0)
    D₆ = (120 : ℝ)^6 * (a * b * c * d * e)^6 ∧
      D₆ = 2985984000000 * (a * b * c * d * e)^6 ∧
      0 < D₆ := by
  dsimp
  let G : Polynomial ℝ :=
      (Polynomial.C a * Polynomial.X + 1) *
      (Polynomial.C b * Polynomial.X + 1) *
      (Polynomial.C c * Polynomial.X + 1) *
      (Polynomial.C d * Polynomial.X + 1) *
      (Polynomial.C e * Polynomial.X + 1)
  let pde : Polynomial ℝ → ℕ → ℝ :=
    fun f n => ((Polynomial.derivative^[n]) f).eval 0
  change
    Matrix.det (fun i j : Fin 6 => pde G (5 + j.1 - i.1)) =
        (120 : ℝ)^6 * (a * b * c * d * e)^6 ∧
      Matrix.det (fun i j : Fin 6 => pde G (5 + j.1 - i.1)) =
        2985984000000 * (a * b * c * d * e)^6 ∧
      0 < Matrix.det (fun i j : Fin 6 => pde G (5 + j.1 - i.1))
  have pde_zero (f : Polynomial ℝ) (n : ℕ) :
      pde f n = (Nat.factorial n : ℝ) * f.coeff n := by
    dsimp [pde]
    rw [← Polynomial.coeff_zero_eq_eval_zero,
      Polynomial.coeff_iterate_derivative, Nat.zero_add,
      Nat.descFactorial_self]
    norm_num [nsmul_eq_mul]
  have hdegA : (Polynomial.C a * Polynomial.X + 1 : Polynomial ℝ).natDegree = 1 := by
    simpa using (Polynomial.natDegree_linear (a := a) (b := 1) ha.ne')
  have hdegB : (Polynomial.C b * Polynomial.X + 1 : Polynomial ℝ).natDegree = 1 := by
    simpa using (Polynomial.natDegree_linear (a := b) (b := 1) hb.ne')
  have hdegC : (Polynomial.C c * Polynomial.X + 1 : Polynomial ℝ).natDegree = 1 := by
    simpa using (Polynomial.natDegree_linear (a := c) (b := 1) hc.ne')
  have hdegD : (Polynomial.C d * Polynomial.X + 1 : Polynomial ℝ).natDegree = 1 := by
    simpa using (Polynomial.natDegree_linear (a := d) (b := 1) hd.ne')
  have hdegE : (Polynomial.C e * Polynomial.X + 1 : Polynomial ℝ).natDegree = 1 := by
    simpa using (Polynomial.natDegree_linear (a := e) (b := 1) he.ne')
  have hpa : (Polynomial.C a * Polynomial.X + 1 : Polynomial ℝ) ≠ 0 := by
    intro h
    rw [h] at hdegA
    norm_num at hdegA
  have hpb : (Polynomial.C b * Polynomial.X + 1 : Polynomial ℝ) ≠ 0 := by
    intro h
    rw [h] at hdegB
    norm_num at hdegB
  have hpc : (Polynomial.C c * Polynomial.X + 1 : Polynomial ℝ) ≠ 0 := by
    intro h
    rw [h] at hdegC
    norm_num at hdegC
  have hpd : (Polynomial.C d * Polynomial.X + 1 : Polynomial ℝ) ≠ 0 := by
    intro h
    rw [h] at hdegD
    norm_num at hdegD
  have hpe : (Polynomial.C e * Polynomial.X + 1 : Polynomial ℝ) ≠ 0 := by
    intro h
    rw [h] at hdegE
    norm_num at hdegE
  have hdeg : G.natDegree = 5 := by
    rw [Polynomial.natDegree_mul
          (mul_ne_zero (mul_ne_zero (mul_ne_zero hpa hpb) hpc) hpd) hpe,
      Polynomial.natDegree_mul (mul_ne_zero (mul_ne_zero hpa hpb) hpc) hpd,
      Polynomial.natDegree_mul (mul_ne_zero hpa hpb) hpc,
      Polynomial.natDegree_mul hpa hpb, hdegA, hdegB, hdegC, hdegD, hdegE]
  have hla : (Polynomial.C a * Polynomial.X + 1 : Polynomial ℝ).leadingCoeff = a := by
    simpa using (Polynomial.leadingCoeff_linear (a := a) (b := 1) ha.ne')
  have hlb : (Polynomial.C b * Polynomial.X + 1 : Polynomial ℝ).leadingCoeff = b := by
    simpa using (Polynomial.leadingCoeff_linear (a := b) (b := 1) hb.ne')
  have hlc : (Polynomial.C c * Polynomial.X + 1 : Polynomial ℝ).leadingCoeff = c := by
    simpa using (Polynomial.leadingCoeff_linear (a := c) (b := 1) hc.ne')
  have hld : (Polynomial.C d * Polynomial.X + 1 : Polynomial ℝ).leadingCoeff = d := by
    simpa using (Polynomial.leadingCoeff_linear (a := d) (b := 1) hd.ne')
  have hle : (Polynomial.C e * Polynomial.X + 1 : Polynomial ℝ).leadingCoeff = e := by
    simpa using (Polynomial.leadingCoeff_linear (a := e) (b := 1) he.ne')
  have hlead : G.leadingCoeff = a * b * c * d * e := by
    simp only [G, Polynomial.leadingCoeff_mul, hla, hlb, hlc, hld, hle]
  have hlow : Matrix.IsLowerTriangular
      (fun i j : Fin 6 => pde G (5 + j.1 - i.1)) := by
    intro i j hij
    have hlt : i.1 < j.1 := by exact hij
    have horder : 5 < 5 + j.1 - i.1 := by omega
    change pde G (5 + j.1 - i.1) = 0
    rw [pde_zero,
      Polynomial.coeff_eq_zero_of_natDegree_lt (hdeg ▸ horder)]
    norm_num
  have hdet : Matrix.det (fun i j : Fin 6 => pde G (5 + j.1 - i.1)) =
      (120 : ℝ)^6 * (a * b * c * d * e)^6 := by
    rw [Matrix.det_of_isLowerTriangular _ hlow]
    have hdiag : ∀ i : Fin 6, pde G (5 + i.1 - i.1) =
        (120 : ℝ) * (a * b * c * d * e) := by
      intro i
      have hi : 5 + i.1 - i.1 = 5 := by omega
      rw [hi, pde_zero]
      have hcoeff : G.coeff 5 = G.leadingCoeff := by
        rw [← hdeg]
        exact Polynomial.coeff_natDegree
      rw [hcoeff, hlead]
      norm_num
    simp_rw [hdiag]
    simp
    ring
  refine ⟨hdet, ?_, ?_⟩
  · rw [hdet]
    norm_num
  · rw [hdet]
    positivity

end MathlibPlus.Analysis
