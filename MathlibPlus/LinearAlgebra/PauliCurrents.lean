import Mathlib

namespace MathlibPlus.LinearAlgebra.PauliCurrents

open scoped ComplexConjugate

/--
Formalization of admitted claim 11372.  The jet entries are arbitrary complex
numbers; the phase and radial currents are respectively the imaginary and real
parts of `conj F * F'`, as in the packet's definitions.
-/
theorem phaseAndRadialCurrentsPauliBilinears (F F' : ℂ) :
    let ψ : Fin 2 → ℂ := ![F, F']
    let X : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
    let Y : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]
    let iY : Matrix (Fin 2) (Fin 2) ℂ := Complex.I • Y
    let j : ℝ := (star F * F').im
    let x : ℝ := (star F * F').re
    ((j : ℂ) = (1 / 2 : ℂ) *
        ∑ i : Fin 2, ∑ k : Fin 2, star (ψ i) * Y i k * ψ k ∧
      (x : ℂ) = (1 / 2 : ℂ) *
        ∑ i : Fin 2, ∑ k : Fin 2, star (ψ i) * X i k * ψ k) ∧
      (Complex.I * (j : ℂ)) = (1 / 2 : ℂ) *
        ∑ i : Fin 2, ∑ k : Fin 2, star (ψ i) * iY i k * ψ k := by
  dsimp
  constructor
  · constructor
    · simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_fin_one, mul_zero,
        zero_mul, add_zero, zero_add]
      rw [Complex.ext_iff]
      constructor <;> simp [Complex.star_def, Complex.conj_I, Complex.mul_re,
        Complex.mul_im] <;> ring
    · simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_fin_one, mul_zero,
        zero_mul, add_zero, zero_add]
      rw [Complex.ext_iff]
      constructor <;> simp [Complex.mul_re, Complex.mul_im] <;> ring
  · simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_fin_one, mul_zero,
      zero_mul, add_zero, zero_add, Matrix.smul_apply]
    rw [Complex.ext_iff]
    constructor <;> simp [Complex.star_def, Complex.conj_I, Complex.mul_re,
      Complex.mul_im] <;> ring

end MathlibPlus.LinearAlgebra.PauliCurrents
