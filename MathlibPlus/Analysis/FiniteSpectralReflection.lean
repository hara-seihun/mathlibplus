import Mathlib

namespace MathlibPlus.Analysis.finiteSpectralReflection

open scoped BigOperators

/-- A multiplicity-preserving finite reflected packet has the same sum after
applying any term function before or after the reflection. -/
theorem reflection_preserves_finite_spectral_sum
    {R : Type*} [AddCommMonoid R]
    (roots : Multiset ℂ) (τ : ℂ → ℂ)
    (hτ : roots.map τ = roots) (T : ℂ → R) :
    (roots.map (fun ρ => T (τ ρ))).sum = (roots.map T).sum := by
  have h := congrArg (fun m : Multiset ℂ => (m.map T).sum) hτ
  simpa [Multiset.map_map, Function.comp_def] using h

end MathlibPlus.Analysis.finiteSpectralReflection
