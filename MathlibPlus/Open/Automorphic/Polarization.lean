import Mathlib

/-!
# Polarization and finite coefficient packets

Statement-fidelity registry node for admitted claim 309 from packet `C-0019`.
The packet does not yet provide canonical Lean declarations for the complete Maaß
word, the two-variable covariance, its polarization projection, or `A_{k,0}`.
Those data therefore remain explicit parameters. The raised local factor is inlined
exactly, and using the same coefficient index on both sides records that projection
neither shifts nor reindexes any finite-place coefficient.
-/

namespace MathlibPlus.Open.Automorphic.Polarization

/-- Projecting only the untouched polarization variable to type `k + 2m`, after the
complete Maaß word has acted in the differentiated variable, multiplies every entry
of the completed coefficient packet by the one scalar
`A_{k,0}(s-1) * β_{k,m}(s)` and preserves its coefficient index. -/
def preservesFiniteCoefficientPacket {ι : Type*}
    (A₀ : ℕ → ℂ → ℂ)
    (maassThenPolarize : ℕ → ℕ → ℂ → ι → ℂ)
    (completedCoefficientRow : ℕ → ℂ → ι → ℂ) : Prop :=
  ∀ (k m : ℕ) (s : ℂ), 0 < k → ∀ i : ι,
    maassThenPolarize k m s i =
      A₀ k (s - 1) *
        (∏ r ∈ Finset.range m,
          (((k + 2 * r + 1 : ℕ) : ℂ) - s) /
            (((k + 2 * r + 1 : ℕ) : ℂ) + s)) *
        completedCoefficientRow k s i

end MathlibPlus.Open.Automorphic.Polarization
