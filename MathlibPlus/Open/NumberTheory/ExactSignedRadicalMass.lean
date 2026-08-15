import Mathlib

namespace MathlibPlus.Open

/-- The signed radical mass, its squarefree specialization at zero, and the
    absolute-value mass obtained by refusing the cancellation. -/
def exactSignedRadicalMassClaim8317 : Prop :=
  ∀ R : ℕ, 0 < R → Squarefree R →
    let μ : ℕ → ℝ := fun h => ((ArithmeticFunction.moebius h : ℤ) : ℝ)
    let σ : ℝ → ℕ → ℝ :=
      fun s N => (∑ d ∈ Nat.divisors N, Real.rpow (d : ℝ) s)
    (∀ w : ℝ,
      (∑ h ∈ Nat.divisors R,
        μ h / Real.rpow (h : ℝ) w * σ (-1 - w) (R / h)) =
        (∏ p ∈ Nat.primeFactors R,
          (1 + Real.rpow (p : ℝ) (-1 - w) - Real.rpow (p : ℝ) (-w)))) ∧
    (∑ h ∈ Nat.divisors R, μ h * σ (-1) (R / h)) = 1 / (R : ℝ) ∧
    (∑ h ∈ Nat.divisors R, |μ h * σ (-1) (R / h)|) =
      (∏ p ∈ Nat.primeFactors R, (2 + 1 / (p : ℝ)))

end MathlibPlus.Open
