import Mathlib

namespace MathlibPlus.Algebra

/--
The divisibility branch of the square-free cyclic-product decomposition.  The
case `p ∣ n` is retained, with the extracted factor `m = n / p`, rather than
silently restricting to coprime `p` and `n`.
-/
def cyclicProduct_divisibility : Prop :=
  ∀ {p n : ℕ}, Nat.Prime p → Squarefree n → p ∣ n →
    ∃ m : ℕ,
      n = p * m ∧
      m = n / p ∧
      p.Coprime m ∧
      Squarefree m ∧
      Nonempty ((ZMod p × ZMod n) ≃+ ((ZMod p × ZMod p) × ZMod m))

end MathlibPlus.Algebra
