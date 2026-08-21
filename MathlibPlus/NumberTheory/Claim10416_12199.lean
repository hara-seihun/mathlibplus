-- UNVERIFIED (native-decide): submitted but not kernel-verified, so it is not built and MathlibPlus.lean does not import it. See unverified.txt.
import Mathlib

namespace MathlibPlus.NumberTheory.Claim10416_12199

/-- Claim 10416, with the point at infinity represented by `none` in `Option`.
The affine chart is the literal equation over `ZMod 5`; `a5` uses the usual
`p + 1 - #E(F_p)` convention, and the roots are checked in `ℂ`. -/
theorem ellipticCurveFixture_claim10416 :
    let AffineE := {p : ZMod 5 × ZMod 5 // p.2 ^ 2 = p.1 ^ 3 + p.1 + 1}
    let EPoints := Option AffineE
    let a5 : ℤ := 5 + 1 - (Fintype.card EPoints : ℤ)
    let P : Polynomial ℤ := Polynomial.X ^ 2 - Polynomial.C a5 * Polynomial.X + Polynomial.C 5
    let PComplex : Polynomial ℂ := Polynomial.X ^ 2 + Polynomial.C 3 * Polynomial.X + Polynomial.C 5
    let rhoPlus : ℂ := (-3 + Complex.I * (Real.sqrt 11 : ℂ)) / 2
    let rhoMinus : ℂ := (-3 - Complex.I * (Real.sqrt 11 : ℂ)) / 2
    Fintype.card EPoints = 9 ∧
      a5 = -3 ∧
      P = Polynomial.X ^ 2 + Polynomial.C 3 * Polynomial.X + Polynomial.C 5 ∧
      PComplex.eval rhoPlus = 0 ∧ PComplex.eval rhoMinus = 0 ∧
      ‖rhoPlus‖ = Real.sqrt 5 ∧ ‖rhoMinus‖ = Real.sqrt 5 := by
  let AffineE := {p : ZMod 5 × ZMod 5 // p.2 ^ 2 = p.1 ^ 3 + p.1 + 1}
  let EPoints := Option AffineE
  let a5 : ℤ := 5 + 1 - (Fintype.card EPoints : ℤ)
  let P : Polynomial ℤ := Polynomial.X ^ 2 - Polynomial.C a5 * Polynomial.X + Polynomial.C 5
  let PComplex : Polynomial ℂ := Polynomial.X ^ 2 + Polynomial.C 3 * Polynomial.X + Polynomial.C 5
  let rhoPlus : ℂ := (-3 + Complex.I * (Real.sqrt 11 : ℂ)) / 2
  let rhoMinus : ℂ := (-3 - Complex.I * (Real.sqrt 11 : ℂ)) / 2
  change Fintype.card EPoints = 9 ∧
    a5 = -3 ∧
    P = Polynomial.X ^ 2 + Polynomial.C 3 * Polynomial.X + Polynomial.C 5 ∧
    PComplex.eval rhoPlus = 0 ∧ PComplex.eval rhoMinus = 0 ∧
    ‖rhoPlus‖ = Real.sqrt 5 ∧ ‖rhoMinus‖ = Real.sqrt 5
  have hcard : Fintype.card EPoints = 9 := by native_decide
  have ha5 : a5 = -3 := by
    dsimp [a5]
    rw [hcard]
    norm_num
  have hP : P = Polynomial.X ^ 2 + Polynomial.C 3 * Polynomial.X + Polynomial.C 5 := by
    dsimp [P]
    rw [ha5]
    norm_num [Polynomial.ext_iff]
  have h11 : (Real.sqrt 11)^2 = (11 : ℝ) := Real.sq_sqrt (by norm_num)
  have hrootPlus : PComplex.eval rhoPlus = 0 := by
    apply Complex.ext <;>
      norm_num [PComplex, rhoPlus, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_pow, pow_two, Complex.div_re, Complex.div_im,
        Complex.normSq_apply, Complex.mul_re, Complex.mul_im] <;>
      nlinarith [h11]
  have hrootMinus : PComplex.eval rhoMinus = 0 := by
    apply Complex.ext <;>
      norm_num [PComplex, rhoMinus, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_pow, pow_two, Complex.div_re, Complex.div_im,
        Complex.normSq_apply, Complex.mul_re, Complex.mul_im] <;>
      nlinarith [h11]
  have hnormPlus : ‖rhoPlus‖ = Real.sqrt 5 := by
    rw [Complex.norm_def, Complex.normSq_apply]
    simp [rhoPlus, Complex.div_re, Complex.div_im, Complex.normSq_apply,
      Complex.mul_re, Complex.mul_im]
    congr 1
    nlinarith
  have hnormMinus : ‖rhoMinus‖ = Real.sqrt 5 := by
    rw [Complex.norm_def, Complex.normSq_apply]
    simp [rhoMinus, Complex.div_re, Complex.div_im, Complex.normSq_apply,
      Complex.mul_re, Complex.mul_im]
    congr 1
    nlinarith
  exact ⟨hcard, ha5, hP, hrootPlus, hrootMinus, hnormPlus, hnormMinus⟩

/-- Claim 12199, using the affine chord-tangent doubling formula at the
specified point.  The two displayed affine points are explicitly checked to
lie on the same curve. -/
theorem ellipticCurveNonIdempotent_claim12199 :
    let AffineE := {p : ZMod 5 × ZMod 5 // p.2 ^ 2 = p.1 ^ 3 + p.1 + 1}
    let EPoints := Option AffineE
    let onCurve : (ZMod 5 × ZMod 5) → Prop := fun p =>
      p.2 ^ 2 = p.1 ^ 3 + p.1 + 1
    let P : Polynomial ℤ := Polynomial.X ^ 2 + Polynomial.C 3 * Polynomial.X + Polynomial.C 5
    let double : (ZMod 5 × ZMod 5) → (ZMod 5 × ZMod 5) := fun p =>
      let m := (3 * p.1 ^ 2 + 1) * (2 * p.2)⁻¹
      let x₂ := m ^ 2 - 2 * p.1
      (x₂, m * (p.1 - x₂) - p.2)
    Fintype.card EPoints = 9 ∧
      onCurve (0, 1) ∧ onCurve (4, 2) ∧
      P = Polynomial.X ^ 2 + Polynomial.C 3 * Polynomial.X + Polynomial.C 5 ∧
      double (0, 1) = (4, 2) ∧
      ((4 : ZMod 5), (2 : ZMod 5)) ≠ ((0 : ZMod 5), (1 : ZMod 5)) := by
  let AffineE := {p : ZMod 5 × ZMod 5 // p.2 ^ 2 = p.1 ^ 3 + p.1 + 1}
  let EPoints := Option AffineE
  let onCurve : (ZMod 5 × ZMod 5) → Prop := fun p =>
    p.2 ^ 2 = p.1 ^ 3 + p.1 + 1
  let P : Polynomial ℤ := Polynomial.X ^ 2 + Polynomial.C 3 * Polynomial.X + Polynomial.C 5
  let double : (ZMod 5 × ZMod 5) → (ZMod 5 × ZMod 5) := fun p =>
    let m := (3 * p.1 ^ 2 + 1) * (2 * p.2)⁻¹
    let x₂ := m ^ 2 - 2 * p.1
    (x₂, m * (p.1 - x₂) - p.2)
  change Fintype.card EPoints = 9 ∧
    onCurve (0, 1) ∧ onCurve (4, 2) ∧
    P = Polynomial.X ^ 2 + Polynomial.C 3 * Polynomial.X + Polynomial.C 5 ∧
    double (0, 1) = (4, 2) ∧
    ((4 : ZMod 5), (2 : ZMod 5)) ≠ ((0 : ZMod 5), (1 : ZMod 5))
  have hcard : Fintype.card EPoints = 9 := by native_decide
  have hcurveP : onCurve (0, 1) := by native_decide
  have hcurveDouble : onCurve (4, 2) := by native_decide
  have hP : P = Polynomial.X ^ 2 + Polynomial.C 3 * Polynomial.X + Polynomial.C 5 := by
    rfl
  have hdouble : double (0, 1) = (4, 2) := by native_decide
  have hne : ((4 : ZMod 5), (2 : ZMod 5)) ≠ ((0 : ZMod 5), (1 : ZMod 5)) := by
    native_decide
  exact ⟨hcard, hcurveP, hcurveDouble, hP, hdouble, hne⟩

end MathlibPlus.NumberTheory.Claim10416_12199
