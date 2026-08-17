import Mathlib
import MathlibPlus.Algebra.PathPalindromeMatchingClaims

namespace MathlibPlus.Open.ResearchFormalization.R0600Claim26296

/-- The four exact factor identities behind the path-palindrome differences. -/
def fourPathPalindromeDifferencesHaveExactQuotients_claim26296 : Prop :=
  ∀ {R : Type*} [CommRing R]
    (x y z u p m n α β : R),
    let h : R := x * (m - n) - p * (z - y)
    let c₀ : R := α * x * p + β * x * m + β * y * p
    let c₁ : R := α * z * p + β * z * m + β * u * p
    let d₀ : R := α * x * p + β * x * n + β * z * p
    let d₁ : R := α * y * p + β * y * n + β * u * p
    (c₀ - d₀ = β * h) ∧
      (x * c₀ - d₀ * x = (β * x) * h) ∧
      (y * c₀ + x * c₁ - d₁ * x - d₀ * z =
        (β * (y + z)) * h) ∧
      (x * (c₁ - d₁) - c₀ * (z - y) = (β * y) * h)

end MathlibPlus.Open.ResearchFormalization.R0600Claim26296
