import Mathlib

namespace MathlibPlus.Open.Research.R5410

open scoped BigOperators

/-- The polynomial `q_p` from the admitted scalar-identity claim. -/
def q_p (p : ℕ) [Fact (Nat.Prime p)] (X Y : ZMod p) : ZMod p :=
  ∑ k ∈ Finset.Icc 1 (p - 1), X ^ k * Y ^ (p - k)

/-- The polynomial `r_p` from the admitted scalar-identity claim. -/
def r_p (p : ℕ) [Fact (Nat.Prime p)] (X Y : ZMod p) : ZMod p :=
  ∑ k ∈ Finset.range p, X ^ k * Y ^ (p - 1 - k)

/-- The map `s` from the admitted scalar-identity claim. -/
def s {p : ℕ} [Fact (Nat.Prime p)] {A B : Type*}
    [AddCommGroup A] [Module (ZMod p) A]
    [AddCommGroup B] [Module (ZMod p) B]
    (ell m n : B →ₗ[ZMod p] ZMod p) (v w : A) (x : B) : A :=
  q_p p (ell x) (m x) • v +
    ((n x) * r_p p (ell x) (m x)) • w

/-- Claim 60566: the scalar identities and oddness of `s`. -/
def scalar_identities_and_oddness (p : ℕ) [Fact (Nat.Prime p)] (hodd : Odd p)
    {A B : Type*} [AddCommGroup A] [Module (ZMod p) A]
    [FiniteDimensional (ZMod p) A]
    [AddCommGroup B] [Module (ZMod p) B]
    [FiniteDimensional (ZMod p) B]
    (ell m n : B →ₗ[ZMod p] ZMod p)
    (hlin : LinearIndependent (ZMod p) ![ell, m, n]) (v w : A) : Prop :=
  (∀ a b : ZMod p,
      (a = b → q_p p a b = -a) ∧
      (a ≠ b → q_p p a b = 0)) ∧
  (∀ a b : ZMod p,
      (a = b → r_p p a b = 0) ∧
      (a ≠ b → r_p p a b = 1)) ∧
  Function.Odd (s ell m n v w)

/-- Claim 60567: the exact constancy criteria for the scalarized difference. -/
def difference_constancy (p : ℕ) [Fact (Nat.Prime p)] (hodd : Odd p)
    {A B : Type*} [AddCommGroup A] [Module (ZMod p) A]
    [FiniteDimensional (ZMod p) A]
    [AddCommGroup B] [Module (ZMod p) B]
    [FiniteDimensional (ZMod p) B]
    (ell m n : B →ₗ[ZMod p] ZMod p)
    (hlin : LinearIndependent (ZMod p) ![ell, m, n]) (v w : A) : Prop :=
  ∀ (d : B) (u : A →ₗ[ZMod p] ZMod p),
    let α : ZMod p := u v
    let β : ZMod p := u w
    let a : ZMod p := ell d
    let b : ZMod p := m d
    let c : ZMod p := n d
    let delta : B → ZMod p :=
      fun x => u (s ell m n v w (x + d) - s ell m n v w x)
    (a = b →
        ((∃ lambda : ZMod p, ∀ x : B, delta x = lambda) ↔
          α * a + β * c = 0) ∧
        (α * a + β * c = 0 → ∀ x : B, delta x = β * c)) ∧
    (a ≠ b →
        ((∃ lambda : ZMod p, ∀ x : B, delta x = lambda) ↔
          (α = 0 ∧ β = 0)) ∧
        ((α = 0 ∧ β = 0) → ∀ x : B, delta x = 0))

end MathlibPlus.Open.Research.R5410
