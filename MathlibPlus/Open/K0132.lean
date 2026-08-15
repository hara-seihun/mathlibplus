import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.K0132

/-- Weighted evaluation at the indexed roots recovers the coefficient moments. -/
def weightedRootFunctionalMoment
    {R : Type*} [Semiring R]
    (B : Type*) (d : ℕ) (r : B → ℕ → R) (b : B) (μ : ℕ → R) : Prop :=
  (∀ k : ℕ, μ k = Finset.sum (Finset.Icc 1 d) (fun j => (r b j) ^ (k + 1))) →
    ∀ k : ℕ,
      let Lb : (R → R) → R :=
        fun f => Finset.sum (Finset.Icc 1 d) (fun j => r b j * f (r b j))
      Lb (fun x => x ^ k) = μ k

end MathlibPlus.Open.K0132
