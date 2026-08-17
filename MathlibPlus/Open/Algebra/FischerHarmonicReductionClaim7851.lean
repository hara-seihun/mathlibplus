import MathlibPlus.Open.Algebra.TwoStepSplitQuotient

namespace MathlibPlus.Open.Algebra

noncomputable section

/-- Fischer harmonic reduction in the fixed split four-space model: the
harmonic kernel and the quadratic-multiple submodule give the degree-`r`
direct sum, while the harmonic carrier is the Cartan component and has the
stated square dimension. -/
def fischerHarmonicReductionClaim7851 : Prop :=
  ∀ r : ℕ,
    harmonicSubmodule r ⊔ quadraticSubmodule r =
        MvPolynomial.homogeneousSubmodule Four Scalar r ∧
      Disjoint (harmonicSubmodule r) (quadraticSubmodule r) ∧
        Nonempty (Harmonic r ≃ₗ[Scalar] CartanComponent r) ∧
          Module.finrank Scalar (Harmonic r) = (r + 1) ^ 2

end
end MathlibPlus.Open.Algebra
