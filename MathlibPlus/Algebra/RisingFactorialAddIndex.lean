import Mathlib

namespace MathlibPlus.Algebra

/--
Claim 42534.  The rising factorial (Mathlib's `ascPochhammer`) factors at an
additive index split, for every complex parameter and natural indices.
-/
theorem risingFactorialAddIndex_claim42534 (α : ℂ) (p q : ℕ) :
    (ascPochhammer ℂ (p + q)).eval α =
      (ascPochhammer ℂ q).eval α *
        (ascPochhammer ℂ p).eval (α + q) := by
  have h := congrArg (fun f : Polynomial ℂ => f.eval α)
    (ascPochhammer_mul ℂ q p)
  simpa [Polynomial.eval_mul, Polynomial.eval_comp, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_natCast, Nat.add_comm, mul_comm] using h.symm

end MathlibPlus.Algebra
