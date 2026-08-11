import MathlibPlus.Basic

namespace MathlibPlus.LinearAlgebra

/-- Claim 11712: an upper-triangular coupling has the same power traces as its
    diagonal part.  The theorem is stated over a semiring and includes the
    zeroth power, which is stronger than the source's positive-power form. -/
theorem upperTriangularTwoByTwo_trace_pow {R : Type*} [Semiring R]
    (a e b : R) :
    ∀ m : ℕ,
      Matrix.trace ((!![a, e; 0, b] : Matrix (Fin 2) (Fin 2) R) ^ m) =
        a ^ m + b ^ m := by
  intro m
  let T : Matrix (Fin 2) (Fin 2) R := !![a, e; 0, b]
  have hprops :
      ∀ n : ℕ,
        (T ^ n) 0 0 = a ^ n ∧
          (T ^ n) 1 0 = 0 ∧
          (T ^ n) 1 1 = b ^ n := by
    intro n
    induction n with
    | zero =>
        simp [T]
    | succ n ih =>
        have h00 : (T ^ (n + 1)) 0 0 = a ^ (n + 1) := by
          rw [pow_succ]
          simp [Matrix.mul_apply, Fin.sum_univ_two, T, ih.1, pow_succ]
        have h10 : (T ^ (n + 1)) 1 0 = 0 := by
          rw [pow_succ]
          simp [Matrix.mul_apply, Fin.sum_univ_two, T, ih.2.1]
        have h11 : (T ^ (n + 1)) 1 1 = b ^ (n + 1) := by
          rw [pow_succ]
          simp [Matrix.mul_apply, Fin.sum_univ_two, T, ih.2.1, ih.2.2,
            pow_succ]
        exact ⟨h00, h10, h11⟩
  have hp := hprops m
  dsimp [T] at hp ⊢
  simp [Matrix.trace, Fin.sum_univ_two, hp.1, hp.2.2]

/-- The same upper-triangular matrix has the characteristic polynomial of its
    diagonal matrix, so over a field it has the same spectrum as that diagonal
    matrix. -/
theorem upperTriangularTwoByTwo_charpoly {R : Type*} [CommRing R]
    [Nontrivial R] (a e b : R) :
    ( !![a, e; 0, b] : Matrix (Fin 2) (Fin 2) R).charpoly =
      (Matrix.diagonal ![a, b] : Matrix (Fin 2) (Fin 2) R).charpoly := by
  rw [Matrix.charpoly_fin_two, Matrix.charpoly_fin_two]
  simp [Matrix.trace, Matrix.det_fin_two, Fin.sum_univ_two]

/-- Over a field, the characteristic-polynomial equality gives equality of
    the matrix spectra. -/
theorem upperTriangularTwoByTwo_spectrum {𝕜 : Type*} [Field 𝕜] (a e b : 𝕜) :
    spectrum 𝕜 (!![a, e; 0, b] : Matrix (Fin 2) (Fin 2) 𝕜) =
      spectrum 𝕜 (Matrix.diagonal ![a, b] : Matrix (Fin 2) (Fin 2) 𝕜) := by
  ext z
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly,
    Matrix.mem_spectrum_iff_isRoot_charpoly,
    upperTriangularTwoByTwo_charpoly]

/-- Claim 10839: the tuned two-rate output has a nonpositive two-by-two Gram
    determinant, with strict negativity exactly off the equality locus. -/
theorem tunedOutput_rateGram_determinant (a b u v : ℝ) :
    let x : ℝ → ℝ := fun r => r * Real.cosh (r * u)
    let y : ℝ → ℝ := fun r => r * Real.cosh (r * v)
    let Q : ℝ → ℝ → ℝ := fun s t => x s * y t + y s * x t
    let D : ℝ := Matrix.det
      (!![Q a a, Q a b; Q b a, Q b b] : Matrix (Fin 2) (Fin 2) ℝ)
    D = - (x a * y b - x b * y a) ^ 2 ∧
      D ≤ 0 ∧
      (x a * y b ≠ x b * y a → D < 0) := by
  dsimp
  have hdet :
      Matrix.det
          (!![(a * Real.cosh (a * u)) * (a * Real.cosh (a * v)) +
                (a * Real.cosh (a * v)) * (a * Real.cosh (a * u)),
              (a * Real.cosh (a * u)) * (b * Real.cosh (b * v)) +
                (a * Real.cosh (a * v)) * (b * Real.cosh (b * u));
              (b * Real.cosh (b * u)) * (a * Real.cosh (a * v)) +
                (b * Real.cosh (b * v)) * (a * Real.cosh (a * u)),
              (b * Real.cosh (b * u)) * (b * Real.cosh (b * v)) +
                (b * Real.cosh (b * v)) * (b * Real.cosh (b * u))]
            : Matrix (Fin 2) (Fin 2) ℝ) =
        - ((a * Real.cosh (a * u)) * (b * Real.cosh (b * v)) -
            (b * Real.cosh (b * u)) * (a * Real.cosh (a * v))) ^ 2 := by
    simp [Matrix.det_fin_two]
    ring
  constructor
  · exact hdet
  constructor
  · rw [hdet]
    exact neg_nonpos.mpr (sq_nonneg _)
  · intro hne
    rw [hdet]
    exact neg_lt_zero.mpr (sq_pos_of_ne_zero (sub_ne_zero.mpr hne))

end MathlibPlus.LinearAlgebra
