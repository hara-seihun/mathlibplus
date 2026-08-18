import MathlibPlus.Open.NumberTheory.Claim9756
import MathlibPlus.Open.NumberTheory.Claim9759
import MathlibPlus.Open.NumberTheory.Claim9764
import MathlibPlus.Open.NumberTheory.LayerGramFactorizationClaim9761

namespace MathlibPlus.Open.NumberTheory.Claim9768

noncomputable section
open scoped BigOperators RealInnerProductSpace

noncomputable def firstWhitenedCoordinate
    (u : MathlibPlus.Open.NumberTheory.FareyHilbert) : ℝ :=
  inner ℝ u
    (MathlibPlus.Open.NumberTheory.Claim9759.fareyWhitened
      MathlibPlus.Open.NumberTheory.fareyBasisVector 1)
    /
    MathlibPlus.Open.NumberTheory.Claim9756.arithmeticWhiteningWeight 1

noncomputable def cutoffVector (N : ℕ) :
    MathlibPlus.Open.NumberTheory.FareyHilbert :=
  ∑ n ∈ Finset.Icc 1 N,
    MathlibPlus.Open.NumberTheory.fareyLevelVector n

noncomputable def cutoffCoefficientSum (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N,
    (MathlibPlus.NumberTheory.Claim9757.fareyConvolutionCoeff n : ℝ)

/-- Claim 9768: the first whitened coordinate of the natural cutoff is
exactly `B(N)`, with the equivalent inner-product identity at `R(1)=1`. -/
def claim9768 : Prop :=
  MathlibPlus.Open.NumberTheory.Claim9756.arithmeticWhiteningWeight 1 = 1 ∧
    ∀ N : ℕ, 0 < N →
      firstWhitenedCoordinate (cutoffVector N) = cutoffCoefficientSum N ∧
      inner ℝ (cutoffVector N)
        (MathlibPlus.Open.NumberTheory.Claim9759.fareyWhitened
          MathlibPlus.Open.NumberTheory.fareyBasisVector 1) =
        cutoffCoefficientSum N

end

end MathlibPlus.Open.NumberTheory.Claim9768
