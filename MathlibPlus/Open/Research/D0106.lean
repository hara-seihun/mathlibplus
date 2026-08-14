import Mathlib

namespace MathlibPlus.Open.Research.D0106

/-- For a finite decoration alphabet and positive integer length slots,
`q` truncates every length at the observation radius. -/
def truncatedLocalSignature
    (B : Type) [Fintype B] (d : ℕ)
    (q : ℕ → (B × (Fin d → ℕ)) → (B × (Fin d → ℕ))) : Prop :=
  ∀ (h : ℕ) (b : B) (ℓ : Fin d → ℕ),
    (∀ i, 0 < ℓ i) →
      q h (b, ℓ) = (b, fun i => min (ℓ i) h)

end MathlibPlus.Open.Research.D0106
