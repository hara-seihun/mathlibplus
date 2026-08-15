import Mathlib

namespace MathlibPlus.Open.Analysis

private def entire (f : ℂ → ℂ) : Prop :=
  Differentiable ℂ f

private def entireFactorOrder (f : ℂ → ℂ) (z : ℂ) (n : ℕ) : Prop :=
  ∃ g : ℂ → ℂ,
    entire g ∧
    (∀ w : ℂ, f w = (w - z) ^ n * g w) ∧
    g z ≠ 0

private noncomputable def zeroOrder (f : ℂ → ℂ) (z : ℂ) : ℕ := by
  classical
  exact if h : ∃ n : ℕ, entireFactorOrder f z n then Nat.find h else 0

private def locallyFiniteDivisor (ν : ℂ → ℕ) : Prop :=
  ∀ K : Set ℂ, IsCompact K → {z | z ∈ K ∧ ν z ≠ 0}.Finite

/-- The common zero divisor of two nonzero entire functions can be removed globally. -/
def globalRemovalOfCommonEntireZeros : Prop :=
  ∀ (𝕊 𝔹 : ℂ → ℂ),
    entire 𝕊 →
    entire 𝔹 →
    (∃ z : ℂ, 𝕊 z ≠ 0) →
    (∃ z : ℂ, 𝔹 z ≠ 0) →
    let ν : ℂ → ℕ := fun z => min (zeroOrder 𝕊 z) (zeroOrder 𝔹 z)
    locallyFiniteDivisor ν ∧
      ∃ d : ℂ → ℂ,
        entire d ∧
        (∀ z : ℂ, zeroOrder d z = ν z) ∧
        ∃ S B : ℂ → ℂ,
          entire S ∧
          entire B ∧
          (∀ z : ℂ, 𝕊 z = d z * S z) ∧
          (∀ z : ℂ, 𝔹 z = d z * B z) ∧
          (∀ z : ℂ, d z ≠ 0 → S z = 𝕊 z / d z) ∧
          (∀ z : ℂ, d z ≠ 0 → B z = 𝔹 z / d z) ∧
          (∀ z : ℂ, S z ≠ 0 ∨ B z ≠ 0)

end MathlibPlus.Open.Analysis
