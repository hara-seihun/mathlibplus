import Mathlib

namespace MathlibPlus.LinearAlgebra.Claim55205

/--
For the displayed `X`, let `D = [I₃ | X]` and `U = [-Xᵀ | I₄]`.
The sum of the seven column tensors `uᵢ ⊗ dᵢ` is zero.  The displayed
matrix sum is the entrywise definition of that tensor sum.
-/
theorem tensorSum_zero :
    let X : Matrix (Fin 3) (Fin 4) ℤ :=
      !![6, 4, 1, 7;
         6, 8, 2, 4;
         0, 0, 9, 1]
    let D : Matrix (Fin 3) (Fin 7) ℤ :=
      !![1, 0, 0, X 0 0, X 0 1, X 0 2, X 0 3;
         0, 1, 0, X 1 0, X 1 1, X 1 2, X 1 3;
         0, 0, 1, X 2 0, X 2 1, X 2 2, X 2 3]
    let U : Matrix (Fin 4) (Fin 7) ℤ :=
      !![-(X 0 0), -(X 1 0), -(X 2 0), 1, 0, 0, 0;
         -(X 0 1), -(X 1 1), -(X 2 1), 0, 1, 0, 0;
         -(X 0 2), -(X 1 2), -(X 2 2), 0, 0, 1, 0;
         -(X 0 3), -(X 1 3), -(X 2 3), 0, 0, 0, 1]
    (∑ i : Fin 7,
      ((fun a b => U a i * D b i) : Matrix (Fin 4) (Fin 3) ℤ)) = 0 := by
  native_decide

end MathlibPlus.LinearAlgebra.Claim55205
