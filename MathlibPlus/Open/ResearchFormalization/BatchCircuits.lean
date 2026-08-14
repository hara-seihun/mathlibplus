import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.BatchCircuits

def circuitWeight {S : Type*} [Fintype S] (q : S → ℚ) : ℚ :=
  ∑ e, q e

def circuitLambda {S : Type*} [Fintype S] (q : S → ℚ) (e : S) : ℚ :=
  q e / circuitWeight q

/-- Uniform-plus-scalar response decomposition for a positive one-dimensional
circuit, including the retained scalarization consequence. -/
def positiveScalarCircuitResponseDecomposition : Prop :=
  ∀ (S V Z : Type*) [Fintype S]
    [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    [AddCommGroup Z] [Module ℚ Z] [FiniteDimensional ℚ Z]
    (ell : S → V) (q : S → ℚ),
    (∀ e, 0 < q e) →
    (∑ e, q e • ell e = 0) →
    (∀ r : S → ℚ,
      (∑ e, r e • ell e = 0) →
        ∃ c : ℚ, ∀ e, r e = c * q e) →
    ∀ a : S → Z,
      ∃! Φ : Submodule.span ℚ (Set.range ell) →ₗ[ℚ] Z,
        (∀ e,
          a e =
            (∑ f, circuitLambda q f • a f) +
              Φ ⟨ell e, Submodule.subset_span (Set.mem_range_self e)⟩) ∧
        (∀ (ψ : Z →ₗ[ℚ] ℚ) (e f : S),
          ψ (a e) - ψ (a f) =
            (ψ.comp Φ) ⟨ell e, Submodule.subset_span (Set.mem_range_self e)⟩ -
              (ψ.comp Φ) ⟨ell f, Submodule.subset_span (Set.mem_range_self f)⟩)

end MathlibPlus.Open.ResearchFormalization.BatchCircuits
