import Mathlib

noncomputable section
open Classical

namespace MathlibPlus.Open.ResearchBatch.Lacunary

/-- Finite-moment lacunary locking under bounded positive absolute-amplitude
multiplicity. -/
def finiteMomentLacunaryLocking : Prop :=
  ∀ (lam θ : ℕ → ℝ) (D : ℕ),
    1 ≤ D →
      (∀ n, 0 < lam n) →
        (∀ n m, n ≠ m → lam n ≠ lam m) →
          let x : ℕ → ℝ := fun n => lam n * θ n
          (∀ t : ℝ, 0 < t →
              Set.Finite {n : ℕ | |x n| = t} ∧
                Set.ncard {n : ℕ | |x n| = t} ≤ D) →
            (∀ q : ℕ, q < D →
              Summable (fun n => |x n| * (lam n) ^ q)) →
              (∃ k : ℕ → ℝ,
                (∀ ℓ, 0 < k ℓ) ∧
                  Filter.Tendsto k Filter.atTop Filter.atTop ∧
                    (∀ ℓ q, q < D →
                      HasSum
                        (fun n => Real.sinh (k ℓ * x n) * (lam n) ^ q)
                        0)) →
                ∀ n, θ n = 0

end MathlibPlus.Open.ResearchBatch.Lacunary

end
