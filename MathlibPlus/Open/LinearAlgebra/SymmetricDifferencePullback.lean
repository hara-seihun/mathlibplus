import Mathlib

namespace MathlibPlus.Open.LinearAlgebra

open scoped symmDiff

/--
Counting-function form of the symmetric-difference pullback.  The finite
subsets in `U`, `V`, and `C` are all represented inside the common finite
ground set `W`, so the two natural embeddings into `W` are literal.  The
counting inner products are the standard ones on these finite function
spaces; the registry records the linear pullback action itself.
-/
def symmetricDifferencePullback_claim21561 : Prop :=
  ∀ (W : Type*) [Fintype W] [DecidableEq W]
    (C U V : Finset (Finset W)),
    (hclosed : ∀ A ∈ U, ∀ B ∈ V, A ∆ B ∈ C) →
      ∃ L : ({c // c ∈ C} → ℝ) →ₗ[ℝ]
          (({u // u ∈ U} × {v // v ∈ V}) → ℝ),
        ∀ (q : {c // c ∈ C} → ℝ)
          (A : {u // u ∈ U}) (B : {v // v ∈ V}),
          ∃ c : {c // c ∈ C},
            c.1 = A.1 ∆ B.1 ∧ L q (A, B) = q c

end MathlibPlus.Open.LinearAlgebra
