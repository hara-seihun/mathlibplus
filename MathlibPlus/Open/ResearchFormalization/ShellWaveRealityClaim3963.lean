import Mathlib

open scoped BigOperators ComplexConjugate

namespace MathlibPlus.Open.ResearchFormalization.ShellWaveRealityClaim3963

/-- Conjugation invariance of a finite shell divisor forces every integer shell
moment to be real. -/
def shellWave_real_of_conjugation_invariant_claim3963 : Prop :=
  ∀ {ι : Type*} [Fintype ι]
    (σ : ι → ι) (m : ι → ℕ) (ω : ι → ℂ),
    Function.Involutive σ →
    (∀ j, m (σ j) = m j) →
    (∀ j, ω (σ j) = conj (ω j)) →
    ∀ n : ℤ,
      ∃ r : ℝ,
        (∑ j, (m j : ℂ) * (ω j) ^ n) = (r : ℂ)

end MathlibPlus.Open.ResearchFormalization.ShellWaveRealityClaim3963
