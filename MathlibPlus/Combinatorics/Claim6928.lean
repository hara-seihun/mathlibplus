import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Ring

namespace MathlibPlus.Combinatorics.Claim6928

/-!
Formalization of claim 6928.  The proof keeps the edge and real evaluation
maps local to the theorem, so this statement introduces no orphan global
source definitions.
-/

/-- A rational polynomial has rational real and imaginary parts after
substitution along any rational affine complex edge. -/
theorem rationalAffineSubstitution (P : Polynomial ℚ) (a b c d : ℚ) :
    ∃ A B : Polynomial ℚ, ∀ t : ℝ,
      Polynomial.eval₂ (Rat.castHom ℂ)
          (((a : ℝ) + (b : ℝ) * t : ℂ) +
            Complex.I * ((c : ℝ) + (d : ℝ) * t : ℂ)) P =
        ((Polynomial.eval₂ (Rat.castHom ℝ) t A : ℝ) : ℂ) +
          Complex.I * ((Polynomial.eval₂ (Rat.castHom ℝ) t B : ℝ) : ℂ) := by
  let edge : ℝ → ℂ := fun t ↦
    (((a : ℝ) + (b : ℝ) * t : ℂ) +
      Complex.I * ((c : ℝ) + (d : ℝ) * t : ℂ))
  let evalR : Polynomial ℚ → ℝ → ℝ := fun Q t ↦
    Polynomial.eval₂ (Rat.castHom ℝ) t Q
  change ∃ A B : Polynomial ℚ, ∀ t : ℝ,
    Polynomial.eval₂ (Rat.castHom ℂ) (edge t) P =
      (evalR A t : ℂ) + Complex.I * (evalR B t : ℂ)
  have hxy : ∀ t : ℝ,
      edge t =
        (evalR (Polynomial.C a + Polynomial.C b * Polynomial.X) t : ℂ) +
          Complex.I *
            (evalR (Polynomial.C c + Polynomial.C d * Polynomial.X) t : ℂ) := by
    intro t
    simp [edge, evalR, Polynomial.eval₂_add, Polynomial.eval₂_mul,
      Polynomial.eval₂_C, Polynomial.eval₂_X]
  have hpow : ∀ n : ℕ, ∃ A B : Polynomial ℚ, ∀ t : ℝ,
      edge t ^ n = (evalR A t : ℂ) + Complex.I * (evalR B t : ℂ) := by
    let x : Polynomial ℚ := Polynomial.C a + Polynomial.C b * Polynomial.X
    let y : Polynomial ℚ := Polynomial.C c + Polynomial.C d * Polynomial.X
    intro n
    induction n with
    | zero =>
        refine ⟨1, 0, ?_⟩
        intro t
        simp [evalR]
    | succ n ih =>
        obtain ⟨A, B, hAB⟩ := ih
        refine ⟨A * x - B * y, A * y + B * x, ?_⟩
        intro t
        rw [pow_succ, hAB, hxy]
        simp [evalR, x, y, Polynomial.eval₂_sub, Polynomial.eval₂_add,
          Polynomial.eval₂_mul]
        apply Complex.ext <;>
          simp [Complex.mul_re, Complex.mul_im] <;>
          ring
  induction P using Polynomial.induction_on' with
  | add P Q ihP ihQ =>
      obtain ⟨A₁, B₁, h₁⟩ := ihP
      obtain ⟨A₂, B₂, h₂⟩ := ihQ
      refine ⟨A₁ + A₂, B₁ + B₂, ?_⟩
      intro t
      rw [Polynomial.eval₂_add, h₁, h₂]
      apply Complex.ext <;>
        simp [evalR, Polynomial.eval₂_add, Complex.add_re, Complex.add_im] <;>
        ring
  | monomial n r =>
      obtain ⟨A, B, hAB⟩ := hpow n
      refine ⟨Polynomial.C r * A, Polynomial.C r * B, ?_⟩
      intro t
      rw [show Polynomial.monomial n r = Polynomial.C r * Polynomial.X ^ n by
        rw [Polynomial.C_mul_X_pow_eq_monomial]]
      rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_pow,
        Polynomial.eval₂_X, hAB]
      simp only [evalR, Polynomial.eval₂_mul, Polynomial.eval₂_C]
      apply Complex.ext <;>
        simp [Complex.mul_re, Complex.mul_im] <;>
        ring

end MathlibPlus.Combinatorics.Claim6928
