import Mathlib

namespace MathlibPlus.Open.GraphTheory

/-- Over a prime cyclic central fibre, every normalized central shear has one
linear shadow that agrees with it on every subset invariant under all normalized
relative derivatives. -/
def primeCentralShearUniversalLinearShadow : Prop :=
  ∀ (p n : ℕ), p.Prime →
    ∀ f : (Fin n → ZMod p) → ZMod p,
      f 0 = 0 →
      ∃ ℓ : (Fin n → ZMod p) →+ ZMod p,
        (∀ d, (∀ x, f (x + d) - f x - f d = 0) → ℓ d = f d) ∧
        ∀ S : Set ((Fin n → ZMod p) × ZMod p),
          (∀ x d z,
            (d, z) ∈ S ↔
              (d, z + (f (x + d) - f x - f d)) ∈ S) →
          (fun u : (Fin n → ZMod p) × ZMod p =>
              (u.1, u.2 + ℓ u.1)) '' S =
            (fun u : (Fin n → ZMod p) × ZMod p =>
              (u.1, u.2 + f u.1)) '' S

end MathlibPlus.Open.GraphTheory
