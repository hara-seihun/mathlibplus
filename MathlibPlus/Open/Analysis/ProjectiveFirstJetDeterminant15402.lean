import Mathlib

namespace MathlibPlus.Open.Analysis

/--
Claim 15402.  The projective first-jet determinant is the denominator-free
representative of the relative logarithmic derivative.  The last conjunct
records the common-factor convention: a common factor remains as a square in
the determinant and must be removed before projective critical data are read.
-/
def claim15402_projectiveFirstJetDeterminant : Prop :=
  ∀ (U : Set ℂ) (S B : ℂ → ℂ),
    AnalyticOnNhd ℂ S U →
    AnalyticOnNhd ℂ B U →
      let Δ : (ℂ → ℂ) → (ℂ → ℂ) → ℂ → ℂ :=
        fun X Y z => X z * deriv Y z - deriv X z * Y z
      let r : ℂ → ℂ := fun z => -B z / S z
      let η : ℂ → ℂ →L[ℂ] ℂ :=
        fun z => (r z)⁻¹ • fderiv ℂ r z
      let dz : ℂ → ℂ →L[ℂ] ℂ :=
        fun _ => ContinuousLinearMap.id ℂ ℂ
      AnalyticOnNhd ℂ (Δ S B) U ∧
        (∀ z : ℂ, z ∈ U → S z * B z ≠ 0 →
          η z = (Δ S B z / (S z * B z)) • dz z) ∧
        (∀ z : ℂ, z ∈ U → S z * B z ≠ 0 →
          deriv r z / r z = Δ S B z / (S z * B z)) ∧
        (∀ H S₀ B₀ : ℂ → ℂ,
          AnalyticOnNhd ℂ H U →
          AnalyticOnNhd ℂ S₀ U →
          AnalyticOnNhd ℂ B₀ U →
          ∀ z : ℂ, z ∈ U →
            Δ (fun w => H w * S₀ w) (fun w => H w * B₀ w) z =
              H z ^ 2 * Δ S₀ B₀ z)

end MathlibPlus.Open.Analysis
