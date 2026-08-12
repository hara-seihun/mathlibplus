import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Tactic

namespace MathlibPlus.Algebra

/-- The rank-two square-base value in the normalization of legacy claim 57477
(packet R-5221, statement (3)). -/
theorem claim57477_squareBaseEvaluation :
    let a : ℚ := 5 / 4
    let p : ℕ → Polynomial ℚ :=
      fun n => Nat.rec 1 (fun _ q =>
        Polynomial.X * q.derivative + (Polynomial.C a - Polynomial.X) * q) n
    let g : ℕ → Polynomial ℚ := fun j => (p (2 * j)).derivative
    let F2 : ℚ → ℚ → ℚ := fun x y =>
      ((g 1).eval x * (g 2).eval y - (g 2).eval x * (g 1).eval y) / (y - x)
    F2 2 8 = 119 / 4 := by
  dsimp
  let step : Polynomial ℚ → Polynomial ℚ := fun q =>
    Polynomial.X * q.derivative + (Polynomial.C (5 / 4) - Polynomial.X) * q
  let p0 : Polynomial ℚ := 1
  let p1 : Polynomial ℚ := step p0
  let p2 : Polynomial ℚ := step p1
  let p3 : Polynomial ℚ := step p2
  let p4 : Polynomial ℚ := step p3
  have hp2 :
      Nat.rec 1 (fun (_ : ℕ) (q : Polynomial ℚ) =>
        Polynomial.X * q.derivative + (Polynomial.C (5 / 4) - Polynomial.X) * q) 2 = p2 := by
    rfl
  have hp4 :
      Nat.rec 1 (fun (_ : ℕ) (q : Polynomial ℚ) =>
        Polynomial.X * q.derivative + (Polynomial.C (5 / 4) - Polynomial.X) * q) 4 = p4 := by
    rfl
  rw [hp2, hp4]
  norm_num [step, p0, p1, p2, p3, p4, Polynomial.derivative_add,
    Polynomial.derivative_sub, Polynomial.derivative_mul, Polynomial.derivative_C,
    Polynomial.derivative_X, Polynomial.derivative_one, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]

end MathlibPlus.Algebra
