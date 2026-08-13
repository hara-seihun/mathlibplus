import Mathlib

namespace MathlibPlus.Open.Algebra

/-- The literal triangular-star identity. The source's `q_d` is unfolded as
`B(s^(d-1)) - s^d`; no assumptions about the source's particular algebraic
carrier are silently added. -/
def triangularStarIdentity_claim23455 : Prop :=
  ∀ {R : Type*} [CommRing R] (B : R → R) (s x₁ : R) (e : ℕ → R),
    ∀ d : ℕ, 2 ≤ d →
      B (s ^ (d - 1)) - s ^ d =
        e d + ∑ j ∈ Finset.Icc 2 (d - 1),
          (Nat.choose (d - 1) (j - 1) : R) * x₁ ^ (d - j) * e j

end MathlibPlus.Open.Algebra

namespace MathlibPlus.Algebra.Claim23455

/-- At `d = 2`, the empty lower-index sum gives `q₂ = e₂`. -/
theorem q_two_eq_e_two {R : Type*} [CommRing R]
    (B : R → R) (s x₁ : R) (e : ℕ → R)
    (h : ∀ d : ℕ, 2 ≤ d →
      B (s ^ (d - 1)) - s ^ d =
        e d + ∑ j ∈ Finset.Icc 2 (d - 1),
          (Nat.choose (d - 1) (j - 1) : R) * x₁ ^ (d - j) * e j) :
    B s - s ^ 2 = e 2 := by
  have h2 := h 2 (by omega)
  simpa using h2

/-- The displayed identity solves for `e d` using only earlier indices. -/
theorem extract_e {R : Type*} [CommRing R]
    (B : R → R) (s x₁ : R) (e : ℕ → R)
    (h : ∀ d : ℕ, 2 ≤ d →
      B (s ^ (d - 1)) - s ^ d =
        e d + ∑ j ∈ Finset.Icc 2 (d - 1),
          (Nat.choose (d - 1) (j - 1) : R) * x₁ ^ (d - j) * e j)
    {d : ℕ} (hd : 2 ≤ d) :
    e d = B (s ^ (d - 1)) - s ^ d -
      ∑ j ∈ Finset.Icc 2 (d - 1),
        (Nat.choose (d - 1) (j - 1) : R) * x₁ ^ (d - j) * e j := by
  have hd' := h d hd
  rw [hd']
  ring

end MathlibPlus.Algebra.Claim23455
