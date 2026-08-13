import MathlibPlus.ComplexGeometry.ReflectedWedge

open scoped Matrix

namespace MathlibPlus.ComplexGeometry

/-- Claim 12148: the polarized root matrix has the displayed reflection symmetry
and determinant.  The source's abbreviations `R_root`, `D_root`, and `K₆` are
represented by the already-defined reflected/direct energies and `rootConeK6`.
-/
theorem polarizedRootMatrix_determinant_claim12148 (x y a b : ℝ) :
    let A : ℝ := Real.sqrt 2 * (x + y) + (x - y)
    let D : ℝ := Real.sqrt 2 * (x + y) - (x - y)
    let d : ℝ := a - b
    let q : Matrix (Fin 2) (Fin 2) ℂ := !![A, Complex.I * d; Complex.I * d, D]
    let r : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]
    let c : Matrix (Fin 2) (Fin 2) ℂ := fun i j => star (q i j)
    q.IsSymm ∧
      q = r * c * r ∧
      Matrix.det q =
        (2 * (x + y) ^ 2 - (x - y) ^ 2 + (a - b) ^ 2 : ℝ) ∧
      Matrix.det q =
        (2 * rootReflectedEnergy (x + a * Complex.I) (y + b * Complex.I) -
          rootDirectEnergy (x + a * Complex.I) (y + b * Complex.I) : ℝ) ∧
      Matrix.det q = (4 * rootConeK6 x y a b : ℝ) := by
  dsimp
  let A : ℝ := Real.sqrt 2 * (x + y) + (x - y)
  let D : ℝ := Real.sqrt 2 * (x + y) - (x - y)
  let d : ℝ := a - b
  let q : Matrix (Fin 2) (Fin 2) ℂ := !![A, Complex.I * d; Complex.I * d, D]
  let r : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]
  let c : Matrix (Fin 2) (Fin 2) ℂ := fun i j => star (q i j)
  have hc : c = !![(A : ℂ), -Complex.I * (d : ℂ); -Complex.I * (d : ℂ), (D : ℂ)] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [c, q]
  have hs : q.IsSymm := by
    apply Matrix.IsSymm.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [q]
  have hreflection : q = r * c * r := by
    rw [hc]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [q, r, Matrix.mul_apply, Fin.sum_univ_two]
  have hdet : Matrix.det q =
      (2 * (x + y) ^ 2 - (x - y) ^ 2 + (a - b) ^ 2 : ℝ) := by
    change Matrix.det (!![(A : ℂ), Complex.I * (d : ℂ); Complex.I * (d : ℂ), (D : ℂ)]) = _
    rw [Matrix.det_fin_two_of]
    have hII : (Complex.I * (d : ℂ)) * (Complex.I * (d : ℂ)) =
        -((d : ℂ) ^ 2) := by
      calc
        (Complex.I * (d : ℂ)) * (Complex.I * (d : ℂ)) =
            (Complex.I * Complex.I) * ((d : ℂ) * (d : ℂ)) := by ring
        _ = -((d : ℂ) ^ 2) := by rw [Complex.I_mul_I]; ring
    rw [hII]
    apply Complex.ext
    · simp only [Complex.mul_re, Complex.add_re, Complex.sub_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.neg_re, Complex.neg_im]
      rw [← Complex.ofReal_pow]
      simp only [Complex.ofReal_re]
      dsimp [A, D, d]
      have hsqrt : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
        Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
      ring_nf
      rw [hsqrt]
      ring
    · simp only [Complex.mul_im, Complex.add_im, Complex.sub_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.neg_re, Complex.neg_im]
      rw [← Complex.ofReal_pow]
      simp only [Complex.ofReal_im]
      ring
  refine ⟨hs, hreflection, hdet, ?_, ?_⟩
  · rw [hdet]
    simp only [rootReflectedEnergy_eq, rootDirectEnergy_eq]
    simp [Complex.normSq_apply]
    ring
  · rw [hdet]
    unfold rootConeK6
    norm_num
    ring

end MathlibPlus.ComplexGeometry
