import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.NewResearch2.R0199

/-- Claim 18757: finite Dirichlet atoms at distinct positive integer bases are
linearly independent when their Dirichlet sum vanishes on a set with an
accumulation point. -/
def claim18757_dirichletAtomIndependence : Prop :=
  ∀ {m : ℕ} (n : Fin m → ℕ)
    (hdistinct : ∀ i j, i ≠ j → n i ≠ n j)
    (hpositive : ∀ i, 0 < n i)
    (S : Set ℂ) (hacc : ∃ z : ℂ,
      ∀ U : Set ℂ, IsOpen U → z ∈ U →
        ∃ w : ℂ, w ∈ U ∩ S ∧ w ≠ z)
    (c : Fin m → ℂ),
    (∀ s : ℂ, s ∈ S →
      ∑ i : Fin m, c i * Complex.exp (-s * Complex.log (n i : ℂ)) = 0) →
      ∀ i, c i = 0

/-- Claim 18758: the full complex Laplace semantics of a finite signed
measure on fixed distinct real support is injective, and this injectivity
passes through a linear boundary presentation. -/
def claim18758_zeroSemanticKernel : Prop :=
  ∀ {m : ℕ} (x : Fin m → ℝ)
    (hdistinct : ∀ i j, i ≠ j → x i ≠ x j),
    (∀ c d : Fin m → ℂ,
      (∀ s : ℂ,
        (∑ i : Fin m, c i * Complex.exp (-s * (x i : ℂ))) =
          ∑ i : Fin m, d i * Complex.exp (-s * (x i : ℂ))) →
      c = d) ∧
    (∀ {V : Type*} [AddCommGroup V] [Module ℂ V]
      (boundary : V →ₗ[ℂ] (Fin m → ℂ)) (v : V),
      ((∀ s : ℂ,
        ∑ i : Fin m, (boundary v) i * Complex.exp (-s * (x i : ℂ)) = 0) ↔
        ∀ i, (boundary v) i = 0) ∧
      ((∀ w : V, (∀ i, (boundary w) i = 0) ↔ w = 0) →
        ((∀ s : ℂ,
          ∑ i : Fin m, (boundary v) i * Complex.exp (-s * (x i : ℂ)) = 0) ↔
          v = 0)))

/-- Claim 18760: within finite support, one-species linear presentations and
unquotiented full Laplace semantics, a faithful nonzero boundary cannot be
semantically zero; an escape must leave at least one of these premises. -/
def claim18760_scopeOfFiniteReliefNoGo : Prop :=
  ∀ {m : ℕ} (x : Fin m → ℝ)
    (hdistinct : ∀ i j, i ≠ j → x i ≠ x j)
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (boundary : V →ₗ[ℂ] (Fin m → ℂ)),
    (∀ w : V, w ≠ 0 → ∃ i, (boundary w) i ≠ 0) →
    ∀ v : V, v ≠ 0 →
      (∀ s : ℂ,
        ∑ i : Fin m, (boundary v) i * Complex.exp (-s * (x i : ℂ)) = 0) →
      False

end MathlibPlus.Open.NewResearch2.R0199
