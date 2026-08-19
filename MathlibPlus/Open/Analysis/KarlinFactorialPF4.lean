import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Analysis.Karlin

/-- Ordinary PF-infinity and negative-real-zero data do not force the centered
factorial-scaled order-four minor to be nonnegative: the exact distinct-root
counterexample carrier is retained. -/
def distinctPositiveReciprocalRootsFactorialPF4Counterexample : Prop :=
  ∃ roots : Fin 13 → ℝ,
    (∀ i, 0 < roots i) ∧
      Function.Injective roots ∧
      let B : Polynomial ℝ :=
        ∏ i : Fin 13, (1 + Polynomial.C (roots i) * Polynomial.X)
      let c : ℕ → ℝ :=
        fun k => (Nat.factorial k : ℝ) * B.coeff k
      (∀ k : ℕ, 0 ≤ B.coeff k) ∧
        Matrix.det (fun i j : Fin 4 => c (3 + j.1 - i.1)) < 0

end MathlibPlus.Open.Analysis.Karlin
