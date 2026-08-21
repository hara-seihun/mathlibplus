-- UNVERIFIED (native-decide): submitted but not kernel-verified, so it is not built and MathlibPlus.lean does not import it. See unverified.txt.
import Mathlib

namespace MathlibPlus.Karlin

/-- Claim 689: the structural-boundary order-four Toeplitz minor for
`G(z) = (1 + 8 z)^2` has the exact negative value `-16384`.
The negative-order entries in the Toeplitz display are represented by zero.
-/
theorem fullPF4StructuralBoundaryCounterexample :
    let G : Polynomial ℝ := (1 + Polynomial.C 8 * Polynomial.X) ^ 2
    let T : Matrix (Fin 4) (Fin 4) ℝ := fun i j =>
      if i.val ≤ j.val + 1 then
        Polynomial.eval 0
          ((Polynomial.derivative^[1 + j.val - i.val]) G)
      else 0
    Matrix.det T = -16384 := by
  dsimp
  let M : Matrix (Fin 4) (Fin 4) ℤ := !![16, 128, 0, 0;
      1, 16, 128, 0;
      0, 1, 16, 128;
      0, 0, 1, 16]
  have h : M.det = -16384 := by native_decide
  have hc := Int.cast_det (R := ℝ) M
  have hM :
      (fun i j : Fin 4 =>
        if i.val ≤ j.val + 1 then
          Polynomial.eval 0
            ((Polynomial.derivative^[1 + j.val - i.val])
              ((1 + Polynomial.C 8 * Polynomial.X) ^ 2))
        else 0) = M.map (fun x : ℤ => (x : ℝ)) := by
    funext i j
    fin_cases i <;> fin_cases j <;>
      simp [M, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_X, Polynomial.eval_C, Polynomial.derivative_pow,
        Polynomial.derivative_add, Polynomial.derivative_mul] <;> norm_num

  rw [hM, ← hc]
  exact_mod_cast h

end MathlibPlus.Karlin
