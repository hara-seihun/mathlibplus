import Mathlib

/-!
# All-order radial Loewner congruence

This registry node formalizes admitted claim 207. The completed zeta radial
kernel, reversed-Bessel `Q` coefficients, confluent matrix, radial main, and
diagonal gauge are all inlined so that the congruence is not weakened to an
implication assuming the desired identification. The four exponent pairs quoted
by the source are retained literally.
-/

open scoped BigOperators

namespace MathlibPlus.Open.Analysis.RadialLoewner

/-- The exact all-order radial congruence and determinant scale for the
completed-zeta confluent negative Loewner matrices. -/
def allOrderCongruenceAndDeterminantScale : Prop :=
  let xi : ℝ → ℝ := fun s =>
    ((1 / 2 : ℂ) * s * (s - 1) *
      Complex.cpow (Real.pi : ℂ) (-(s : ℂ) / 2) *
      Complex.Gamma ((s : ℂ) / 2) * riemannZeta s).re
  let X : ℝ → ℝ := fun r => xi (1 / 2 + r)
  let L : ℝ → ℝ := fun r => deriv X r / X r
  let H : ℝ → ℝ := fun x => L (Real.sqrt x) / Real.sqrt x
  let Q : ℕ → ℝ → ℝ := fun n r =>
    ∑ k ∈ Finset.range (n + 1),
      (-1 : ℝ) ^ k *
        (((2 * n - k).factorial : ℝ) /
          ((2 : ℝ) ^ (n - k) * ((n - k).factorial : ℝ) * (k.factorial : ℝ))) *
        (r ^ k * iteratedDeriv k L r)
  let C : (n : ℕ) → ℝ → Matrix (Fin n) (Fin n) ℝ := fun n r i j =>
    (-1 : ℝ) ^ (i.val + j.val + 1) *
      iteratedDeriv (i.val + j.val + 1) H (r ^ 2) /
        ((i.val + j.val + 1).factorial : ℝ)
  let M : (n : ℕ) → ℝ → Matrix (Fin n) (Fin n) ℝ := fun n r i j =>
    Q (i.val + j.val + 1) r / ((i.val + j.val + 1).factorial : ℝ)
  let D : (n : ℕ) → ℝ → Matrix (Fin n) (Fin n) ℝ := fun n r =>
    Matrix.diagonal fun j =>
      (-1 : ℝ) ^ j.val / ((2 : ℝ) ^ j.val * r ^ (2 * j.val))
  (∀ (n : ℕ), 1 ≤ n → ∀ r : ℝ, 0 < r →
    C n r = (1 / (2 * r ^ 3)) • (D n r * M n r * D n r) ∧
    Matrix.det (C n r) =
      Matrix.det (M n r) /
        ((2 : ℝ) ^ (n ^ 2) * r ^ (n * (2 * n + 1)))) ∧
  (6 ^ 2 = 36 ∧ 6 * (2 * 6 + 1) = 78) ∧
  (7 ^ 2 = 49 ∧ 7 * (2 * 7 + 1) = 105) ∧
  (9 ^ 2 = 81 ∧ 9 * (2 * 9 + 1) = 171) ∧
  (10 ^ 2 = 100 ∧ 10 * (2 * 10 + 1) = 210)

end MathlibPlus.Open.Analysis.RadialLoewner
