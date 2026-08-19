import Mathlib

noncomputable section

namespace MathlibPlus.Open.NumberTheory.Claim45362CRTAvoid

/-- Claim 45362: CRT chooses one residue for the controlled shift window at
all primes in a finite large-prime set while retaining an arbitrary Q residue. -/
def claim45362_crtAllAvoidRouteObstruction : Prop :=
  ∀ (K : ℕ), 1 ≤ K →
    ∀ (P : Finset ℕ),
      (∀ p ∈ P, Nat.Prime p ∧ K < p) →
      ∀ (Q : ℕ), 0 < Q →
        (∀ p ∈ P, Nat.Coprime Q p) →
        ∀ r : ℤ, ∃ n : ℤ,
          Int.ModEq Q n r ∧
            ∀ p ∈ P,
              Int.ModEq p n (K + 1 : ℤ) ∧
                ∀ k : ℕ, 1 ≤ k → k ≤ K →
                  ¬((p : ℤ) ∣ n - (k : ℤ))

end MathlibPlus.Open.NumberTheory.Claim45362CRTAvoid
