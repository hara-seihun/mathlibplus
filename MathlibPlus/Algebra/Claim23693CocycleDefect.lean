import Mathlib

namespace MathlibPlus.Algebra.Claim23693

/--
The displayed primitive-line Hochschild-defect polynomial from claim 23693 is
nonzero over `ℤ`.  Variables `0,1` represent the left tensor factor's `s,e₂`
and variables `2,3` the right tensor factor's `s,e₂`.
-/
theorem primitiveLineCocycleDefect_nonzero_claim23693 :
    let defect : MvPolynomial (Fin 4) ℤ :=
      MvPolynomial.X 0 * MvPolynomial.X 2 +
          MvPolynomial.X 1 * MvPolynomial.X 3 - MvPolynomial.X 1 -
        MvPolynomial.X 3
    defect ≠ 0 := by
  dsimp
  intro h
  have h23 : (2 : Fin 4) ≠ 3 := by decide
  have h03 : (0 : Fin 4) ≠ 3 := by decide
  have h13 : (1 : Fin 4) ≠ 3 := by decide
  have hv := congrArg
    (MvPolynomial.eval (fun i : Fin 4 => if i = 3 then 1 else 0)) h
  norm_num [MvPolynomial.eval, h23, h03, h13] at hv

end MathlibPlus.Algebra.Claim23693
