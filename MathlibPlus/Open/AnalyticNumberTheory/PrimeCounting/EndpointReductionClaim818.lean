import Mathlib

namespace MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting

/-! Statement-fidelity registry node for admitted claim 818.  The finite
candidate set keeps the actual endpoints and prime jump points; the no-prime
interval condition is the literal carrier of "decreases between consecutive
primes and jumps only at primes." -/

/-- Claim 818: on a finite prime-step interval, a maximum is attained at the
starting endpoint, a prime jump point, or the final handoff endpoint, and a
left limit at an interior prime is not itself a maximizer. -/
def endpointReduction_claim818 : Prop :=
  ∀ (a b : ℝ) (objective : ℝ → ℝ),
    a ≤ b →
    let isPrime : ℝ → Prop := fun x =>
      ∃ p : ℕ, Nat.Prime p ∧ x = (p : ℝ)
    let interval : Set ℝ := Set.Icc a b
    let candidates : Set ℝ :=
      ({a, b} : Set ℝ) ∪ (interval ∩ {x : ℝ | isPrime x})
    (∀ x y : ℝ, a ≤ x → x < y → y ≤ b →
      (∀ p : ℕ, Nat.Prime p →
        ¬ (x < (p : ℝ) ∧ (p : ℝ) ≤ y)) →
      objective y < objective x) →
    (∃ x : ℝ, x ∈ candidates ∧
      ∀ y : ℝ, y ∈ interval → objective y ≤ objective x) ∧
    (∀ p : ℕ, Nat.Prime p → a < (p : ℝ) → (p : ℝ) < b →
      ∀ ℓ : ℝ,
        Filter.Tendsto objective
          (nhdsWithin (p : ℝ) (Set.Iio (p : ℝ))) (nhds ℓ) →
          ¬ IsGreatest (objective '' interval) ℓ)

end MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting
