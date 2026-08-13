import Mathlib

open scoped BigOperators
open MeasureTheory

namespace MathlibPlus.Open.Analysis.Claim51068

/--
A finite nonnegative measure supported on `[0, 1]` gives positive semidefinite
base, shifted, and upper-localizing Hankel matrices.  The three associated
quadratic forms are the integrals against `1`, `x`, and `1 - x`.
-/
noncomputable def hausdorffMomentMatricesPosSemidef_claim51068 : Prop :=
  ∀ (h : ℕ → ℝ) (μ : Measure ℝ),
    IsFiniteMeasure μ →
      μ (Set.Icc (0 : ℝ) 1)ᶜ = 0 →
        (∀ k : ℕ, h k = ∫ x : ℝ, x ^ k ∂μ) →
          ∀ m : ℕ,
            let H₀ : Matrix (Fin m) (Fin m) ℝ :=
              fun i j => h (i.1 + j.1)
            let H₁ : Matrix (Fin m) (Fin m) ℝ :=
              fun i j => h (i.1 + j.1 + 1)
            let HΔ : Matrix (Fin m) (Fin m) ℝ :=
              fun i j => h (i.1 + j.1) - h (i.1 + j.1 + 1)
            (H₀.PosSemidef ∧ H₁.PosSemidef ∧ HΔ.PosSemidef) ∧
              (∀ v : Fin m → ℝ,
                (∑ i : Fin m, ∑ j : Fin m,
                    v i * h (i.1 + j.1) * v j) =
                  ∫ x : ℝ, (∑ i : Fin m, v i * x ^ i.1) ^ 2 ∂μ) ∧
              (∀ v : Fin m → ℝ,
                (∑ i : Fin m, ∑ j : Fin m,
                    v i * h (i.1 + j.1 + 1) * v j) =
                  ∫ x : ℝ, x * (∑ i : Fin m, v i * x ^ i.1) ^ 2 ∂μ) ∧
              (∀ v : Fin m → ℝ,
                (∑ i : Fin m, ∑ j : Fin m,
                    v i * (h (i.1 + j.1) - h (i.1 + j.1 + 1)) * v j) =
                  ∫ x : ℝ, (1 - x) * (∑ i : Fin m, v i * x ^ i.1) ^ 2 ∂μ)

end MathlibPlus.Open.Analysis.Claim51068
