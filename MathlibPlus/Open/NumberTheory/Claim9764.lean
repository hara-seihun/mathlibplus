import MathlibPlus.Open.NumberTheory.Claim9759
import MathlibPlus.NumberTheory.Claim9757

namespace MathlibPlus.Open.NumberTheory.Claim9764

open scoped BigOperators

noncomputable section

/-- Natural cutoffs expressed in the whitened divisor coordinates. -/
def naturalCutoffInOrthogonalCoordinates : Prop :=
  ∀ {V : Type*} [SeminormedAddCommGroup V] [InnerProductSpace ℝ V]
    (e : ℕ → V),
    (∀ d u : ℕ, 0 < d → 0 < u →
      inner ℝ (e d) (e u) =
        ((Nat.gcd d u : ℝ) ^ 2) / ((d : ℝ) * (u : ℝ))) →
    ∀ N : ℕ, 0 < N →
      let u_N : V :=
        ∑ n ∈ Finset.Icc 1 N,
          MathlibPlus.Open.NumberTheory.Claim9759.fareyLevel e n
      let h : ℕ → ℝ := fun n =>
        (MathlibPlus.NumberTheory.Claim9757.fareyConvolutionCoeff n : ℝ)
      let B : ℕ → ℝ := fun x =>
        ∑ n ∈ Finset.Icc 1 x, h n
      u_N =
        ∑ q ∈ Finset.Icc 1 N,
          B (N / q) •
            MathlibPlus.Open.NumberTheory.Claim9759.fareyWhitened e q

end

end MathlibPlus.Open.NumberTheory.Claim9764
