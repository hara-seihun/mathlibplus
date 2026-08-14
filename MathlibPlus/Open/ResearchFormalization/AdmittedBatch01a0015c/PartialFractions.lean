import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

open scoped BigOperators

/-- Claim 3222: reciprocal partial fractions and the positive and negative
structural moments. -/
def claim3222 : Prop :=
  ∀ (N : ℕ) (x : Fin N → ℂ),
    (∀ ν, x ν ≠ 0) →
    (∀ ν μ, ν ≠ μ → x ν ≠ x μ) →
      let F : ℂ → ℂ := fun z => ∏ ν : Fin N, (1 + x ν * z)
      let H : ℂ → ℂ := fun t => (F (-t))⁻¹
      let c : Fin N → ℂ := fun ν =>
        ∏ μ ∈ (Finset.univ.filter (fun μ : Fin N => μ ≠ ν)),
          (1 - x μ / x ν)⁻¹
      let h : ℕ → ℂ := fun n =>
        iteratedDeriv n H 0 / (Nat.factorial n : ℂ)
      (∀ t : ℂ, F (-t) ≠ 0 →
          H t = ∑ ν : Fin N, c ν / (1 - x ν * t)) ∧
        (∀ n : ℕ, h n = ∑ ν : Fin N, c ν * x ν ^ n) ∧
        (∀ n : ℤ, -(N : ℤ) < n → n < 0 →
          ∑ ν : Fin N, c ν * x ν ^ n = 0)

end MathlibPlus.Open.ResearchFormalization
