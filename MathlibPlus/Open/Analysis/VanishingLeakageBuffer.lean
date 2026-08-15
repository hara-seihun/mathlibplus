import Mathlib

open scoped Topology

namespace MathlibPlus.Open.Analysis

/--
Vanishing leakage leaves a fixed exterior buffer between every full node
outside the enlarged reference interval and the trailing spectrum.
-/
def vanishingLeakage_fixedExteriorBuffer
    (fullNodes : ℕ → Set ℝ)
    (trailingSpectrum : ℕ → Set ℝ)
    (A B xiPlus xiMinus : ℕ → ℝ)
    (δ : ℝ) :
    Prop :=
  0 < δ →
    (∀ N, A N < B N) →
    (∀ N, 0 ≤ xiPlus N ∧ 0 ≤ xiMinus N) →
    (∀ N, trailingSpectrum N ⊆
      Set.Icc (A N - δ / 2 - xiMinus N) (B N + δ / 2 + xiPlus N)) →
    Filter.Tendsto (fun N : ℕ => xiPlus N + xiMinus N) Filter.atTop (𝓝 0) →
      ∀ᶠ N in Filter.atTop,
        ∀ x ∈ fullNodes N,
          x ∉ Set.Icc (A N - δ) (B N + δ) →
            ∀ y ∈ trailingSpectrum N, δ / 4 ≤ dist x y

end MathlibPlus.Open.Analysis
