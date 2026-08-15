import Mathlib

namespace MathlibPlus.Open.D0076

/-- The differential ratio attached to relation data `(q, r)`. -/
def differentialRatio {K : Type*} [Field K] (q : K) (r : ℕ → K) (n : ℕ) : K :=
  r n / (q * r (n - 1))

/-- Differential ratios are invariant under every shape-preserving grading gauge.

The units `c` and `γ₀` describe the exact reachable-data action
`(q, rₙ) ↦ (c q, γ₀ cⁿ rₙ)`. -/
def differentialRatioGaugeInvariant {K : Type*} [Field K] (q : K) (r : ℕ → K) : Prop :=
  ∀ (c γ₀ : Kˣ) (n : ℕ),
    1 ≤ n →
    r (n - 1) ≠ 0 →
      differentialRatio ((c : K) * q)
          (fun k => (γ₀ : K) * (c : K) ^ k * r k) n =
        differentialRatio q r n

end MathlibPlus.Open.D0076
