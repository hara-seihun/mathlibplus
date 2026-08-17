import MathlibPlus.Open.UnnormalizedQuantizedRelation

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.D0075Claim5011

open MathlibPlus.Open.UnnormalizedQuantizedRelation

noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def depthValues_claim5011 (n : ℕ) : Finset ℕ :=
  Finset.range (n - 1) ∪ {n}

def normalizedLiftPow_claim5011 :
    (m k : ℕ) →
      FiniteSimpleGraph.Space m →ₗ[ℚ]
        FiniteSimpleGraph.Space (m + k)
  | m, 0 => LinearMap.id
  | m, k + 1 =>
      (normalizedLift (m + k)).comp (normalizedLiftPow_claim5011 m k)

def transportSpace_claim5011 {a b : ℕ} (h : a = b) :
    FiniteSimpleGraph.Space a →ₗ[ℚ] FiniteSimpleGraph.Space b :=
  h ▸ LinearMap.id

def depthOperator_claim5011 (n : ℕ) :
    Module.End ℚ (FiniteSimpleGraph.Space n) :=
  normalizedUpperPrevious n ∘ₗ lower n

def depthSpace_claim5011 (n k : ℕ) (hkn : k ≤ n) :
    Submodule ℚ (FiniteSimpleGraph.Space n) :=
  Submodule.map
    ((transportSpace_claim5011 (Nat.sub_add_cancel hkn)).comp
      (normalizedLiftPow_claim5011 (n - k) k))
    (LinearMap.ker (lower (n - k)))

def depthLagrangePolynomial_claim5011 (n k : ℕ) : Polynomial ℚ :=
  ∏ j ∈ (depthValues_claim5011 n).erase k,
    Polynomial.C (((k : ℚ) - (j : ℚ))⁻¹) *
      (Polynomial.X - Polynomial.C (j : ℚ))

def depthProjector_claim5011 (n : ℕ)
    (k : {j : ℕ // j ∈ depthValues_claim5011 n}) :
    Module.End ℚ (FiniteSimpleGraph.Space n) :=
  Polynomial.aeval (depthOperator_claim5011 n)
    (depthLagrangePolynomial_claim5011 n k.1)

def deckNullProjector_claim5011 (n : ℕ)
    (h0 : 0 ∈ depthValues_claim5011 n) :
    Module.End ℚ (FiniteSimpleGraph.Space n) :=
  Polynomial.aeval (depthOperator_claim5011 n)
    (∏ j ∈ (depthValues_claim5011 n).erase 0,
      Polynomial.C ((-(j : ℚ))⁻¹) *
        (Polynomial.X - Polynomial.C (j : ℚ)))

def depthDiagonalizable_claim5011 (n : ℕ) : Prop :=
  ∃ ι : Type, ∃ b : Module.Basis ι ℚ (FiniteSimpleGraph.Space n),
    ∃ eigenvalue : ι → ℚ,
      (∀ i, depthOperator_claim5011 n (b i) =
        eigenvalue i • b i) ∧
      (∀ i, ∃ k : ℕ,
        k ∈ depthValues_claim5011 n ∧ eigenvalue i = (k : ℚ))

def claim5011 : Prop :=
  ∀ n : ℕ,
    depthDiagonalizable_claim5011 n ∧
      (∀ μ : ℚ,
        (depthOperator_claim5011 n).HasEigenvalue μ ↔
          ∃ k : ℕ,
            k ∈ depthValues_claim5011 n ∧ μ = (k : ℚ)) ∧
      (∀ k : ℕ, k ∈ depthValues_claim5011 n →
        ∀ hkn : k ≤ n,
          depthSpace_claim5011 n k hkn =
            (depthOperator_claim5011 n).eigenspace (k : ℚ)) ∧
      (0 ∈ depthValues_claim5011 n →
        (depthOperator_claim5011 n).eigenspace 0 =
          LinearMap.ker (lower n)) ∧
      (∀ k : ℕ, ∀ hk : k ∈ depthValues_claim5011 n,
        let p := depthLagrangePolynomial_claim5011 n k
        let P := depthProjector_claim5011 n ⟨k, hk⟩
        Polynomial.eval (k : ℚ) p = 1 ∧
          (∀ j : ℕ, j ∈ depthValues_claim5011 n → j ≠ k →
            Polynomial.eval (j : ℚ) p = 0) ∧
          LinearMap.range P =
            (depthOperator_claim5011 n).eigenspace (k : ℚ) ∧
          P.comp P = P ∧
          (∀ x, x ∈ (depthOperator_claim5011 n).eigenspace (k : ℚ) →
            P x = x) ∧
          (∀ j : ℕ, j ∈ depthValues_claim5011 n → j ≠ k →
            ∀ x, x ∈ (depthOperator_claim5011 n).eigenspace (j : ℚ) →
              P x = 0)) ∧
      (∀ h0 : 0 ∈ depthValues_claim5011 n,
        LinearMap.range (deckNullProjector_claim5011 n h0) =
          LinearMap.ker (lower n))

end
end MathlibPlus.Open.ResearchFormalization.D0075Claim5011
