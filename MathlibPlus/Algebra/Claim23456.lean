import Mathlib

/-!
# Root-closure propagation on kernel generators (claim 23456)

The source's ambient polynomial algebra and root-closure operator are exposed
as an explicit interface.  The theorem proves the all-order propagation from
that interface rather than silently inventing those source definitions.
-/

namespace MathlibPlus.Algebra.Claim23456

theorem rootClosurePropagation_claim23456
    {R : Type*} [CommSemiring R]
    (A : Set R) (B : R → R) (z x₁ : R) (e : ℕ → R)
    (hroot : ∀ {p : R}, p ∈ A → B p ∈ A)
    (hbase : ∀ (b : ℕ) {r : ℕ}, 2 ≤ r → x₁ ^ b * e r ∈ A)
    (hcommute : ∀ (a : ℕ) (p : R),
      B (z ^ a * p) = z ^ a * B p)
    (hidentity : ∀ (b : ℕ) {r : ℕ}, 2 ≤ r →
      B (x₁ ^ b * e r) = z * x₁ ^ b * e r) :
    ∀ (a b r : ℕ), 2 ≤ r → z ^ a * x₁ ^ b * e r ∈ A := by
  intro a
  induction a with
  | zero =>
      intro b r hr
      simpa using hbase b hr
  | succ a ih =>
      intro b r hr
      have hprev : z ^ a * (x₁ ^ b * e r) ∈ A := by
        simpa [mul_assoc] using ih b r hr
      have hclosed : B (z ^ a * (x₁ ^ b * e r)) ∈ A :=
        hroot hprev
      rw [hcommute a, hidentity b hr] at hclosed
      simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using hclosed

end MathlibPlus.Algebra.Claim23456
