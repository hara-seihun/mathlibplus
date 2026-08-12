import MathlibPlus.Basic

open Finset

namespace MathlibPlus.LinearAlgebra.Claim14499

/--
Formalization of admitted claim 14499.  A finite Vandermonde system with
pairwise distinct nodes has only the zero coefficient vector in its kernel.
The source's finite field is instantiated here by `ℚ`, retaining the exact
finite quantifier range `q : Fin m`.
-/
theorem finiteVandermondeCoefficientExtraction
    {m : ℕ} (nodes a : Fin m → ℚ) (hnodes : Function.Injective nodes)
    (h : ∀ q : Fin m, ∑ j, a j * nodes j ^ (q : ℕ) = 0) :
    a = 0 := by
  exact Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hnodes h

end MathlibPlus.LinearAlgebra.Claim14499
