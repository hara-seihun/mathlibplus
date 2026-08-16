import Mathlib

namespace MathlibPlus.Open.Formalization

/-- The set of directions along which the first difference of `f` is constant. -/
def P_f (p : ℕ) {B : Type*} [AddGroup B] (f : B → ZMod p) : Set B :=
  {b | ∃ c : ZMod p, ∀ x : B, f (x + b) - f x = c}

/-- Exact open formalization of admitted claim 60337. -/
def claim60337 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (hpodd : Odd p)
    (B : Type*) [AddCommGroup B] [Module (ZMod p) B]
    [FiniteDimensional (ZMod p) B] (f : B → ZMod p),
    f 0 = 0 →
    ∃ P : Submodule (ZMod p) B,
      (∀ b : B, b ∈ P ↔ b ∈ P_f p f) ∧
      (∃ fP : P →ₗ[ZMod p] ZMod p,
        ∀ b : P, fP b = f (b : B)) ∧
      (∃ ell : B →ₗ[ZMod p] ZMod p,
        ∀ b : P, ell (b : B) = f (b : B))

end MathlibPlus.Open.Formalization
