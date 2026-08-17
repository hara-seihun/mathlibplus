import MathlibPlus.Open.UnnormalizedQuantizedRelation

namespace MathlibPlus.Open.ResearchFormalizationD0075

open MathlibPlus.Open.UnnormalizedQuantizedRelation

noncomputable def degreeScaledLift (c : ℕ → ℚ) (n : ℕ) :
    FiniteSimpleGraph.Space n →ₗ[ℚ] FiniteSimpleGraph.Space (n + 1) :=
  c n • FiniteSimpleGraph.genericLift (n := n)

noncomputable def degreeScaledUpperPrevious (c : ℕ → ℚ) (n : ℕ) :
    FiniteSimpleGraph.Space (n - 1) →ₗ[ℚ] FiniteSimpleGraph.Space n :=
  match n with
  | 0 => 0
  | m + 1 => c m • FiniteSimpleGraph.genericLift (n := m)

noncomputable def degreeScaledCommutator (c : ℕ → ℚ) (n : ℕ) :
    FiniteSimpleGraph.Space n →ₗ[ℚ] FiniteSimpleGraph.Space n :=
  FiniteSimpleGraph.deck (n := n) ∘ₗ degreeScaledLift c n -
    (degreeScaledUpperPrevious c n ∘ₗ lower n)

/-- Claim 5007: among nonzero degree-only rescalings, a degree-independent
scalar commutator is exactly a common nonzero scalar times the reviewed
`2⁻ⁿ` normalization; commutator `1` fixes that common scalar. -/
def uniquenessOfGradingOnlyNormalization_claim5007 : Prop :=
  ∀ c : ℕ → ℚ,
    (∀ n : ℕ, c n ≠ 0) →
    ∀ r : ℚ,
      (∀ n : ℕ,
        degreeScaledCommutator c n = r • LinearMap.id) →
      ∃ a : ℚ,
        a ≠ 0 ∧
          (∀ n : ℕ, c n = a * ((2 : ℚ) ^ n)⁻¹) ∧
          r = a ∧
          (r = 1 ↔ ∀ n : ℕ, c n = ((2 : ℚ) ^ n)⁻¹)

end MathlibPlus.Open.ResearchFormalizationD0075
