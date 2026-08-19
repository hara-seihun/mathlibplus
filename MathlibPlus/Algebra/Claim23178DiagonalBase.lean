import MathlibPlus.Open.ResearchFormalization.ScalarRootedFactors

namespace MathlibPlus.Algebra.Claim23178

open MathlibPlus.Open.ResearchFormalization

noncomputable section

/-- The ambient polynomial subalgebra with no `z` variable. -/
def coefficientOnlyCarrier23178 : Set RootRing :=
  {P | ∃ q : CoefficientRing, P = Polynomial.C q}

/-- The exact `id ⊗ 𝓑` map on the diagonal relative tensor product,
with its balanced left-linearity criterion made explicit. -/
def secondLegRootClosureWellDefined23178
    (B : Subalgebra ℚ RootRing) : Prop :=
  (∃ T : TensorProduct B RootRing RootRing →ₗ[B]
      TensorProduct B RootRing RootRing,
      ∀ a a' : RootRing,
        T (TensorProduct.tmul B a a') =
          TensorProduct.tmul B a (rootClosure a')) ∧
    (∀ b : RootRing, b ∈ B → ∀ a : RootRing,
      rootClosure (b * a) = b * rootClosure a)

/-- A diagonal base is a subalgebra of the scalar rooted-factor algebra; the
central and equal-source/target conditions are written on the ambient carrier. -/
def diagonalCentralBase23178 (B : Subalgebra ℚ RootRing) : Prop :=
  B ≤ scalarRootedFactorAlgebra ∧
    ∀ b : RootRing, b ∈ B → ∀ a : RootRing, b * a = a * b

/-- Every diagonal base for which the second root-closure leg is well-defined
is contained in the `z`-independent part of the scalar rooted-factor algebra. -/
def everyAdmissibleDiagonalBaseIsZIndependent_claim23178 : Prop :=
  ∀ B : Subalgebra ℚ RootRing,
    diagonalCentralBase23178 B →
    secondLegRootClosureWellDefined23178 B →
    ∀ b : RootRing, b ∈ B →
      b ∈ scalarRootedFactorAlgebra ∧ b ∈ coefficientOnlyCarrier23178

end

end MathlibPlus.Algebra.Claim23178
