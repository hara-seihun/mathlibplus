import Mathlib

/-!
# Sufficiently-large-prime Graham rearrangement theorem

Statement-fidelity registry node for admitted claim 16770.  The source says
"once p is sufficiently large", so the threshold is existential and no finite
exceptional set or numerical threshold is introduced.
-/

namespace MathlibPlus.Open.NumberTheory

/-- Claim 16770: for every sufficiently large prime, every subset of the
nonzero elements of `F_p` admits an ordering with pairwise distinct nonempty
partial sums. -/
def sufficientlyLargePrimeGraham : Prop :=
  ∃ p₀ : ℕ, ∀ p : ℕ, Nat.Prime p → p₀ ≤ p →
    ∀ A : Finset (ZMod p), 0 ∉ A →
      ∃ f : Fin A.card → ZMod p,
        Function.Injective f ∧
        Finset.univ.image f = A ∧
        Function.Injective (fun i : Fin A.card =>
          ∑ j ∈ (Finset.univ.filter (fun j : Fin A.card => j ≤ i)), f j)

end MathlibPlus.Open.NumberTheory
