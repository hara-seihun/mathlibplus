import MathlibPlus.Open.ResearchFormalization.Claim17086

namespace MathlibPlus.Open.ResearchFormalization.Claim17085

noncomputable section

open MathlibPlus.Open.FormalizationBatch
open MathlibPlus.Open.ResearchFormalization

/-- Claim 17085: preservation of the two-dimensional span by each pointed
involution forces the exact identity-versus-affine-reflection dichotomy. -/
def claim17085_twoDimensionalActionDichotomy : Prop :=
  ∀ (n : ℕ), 0 < n →
    ∀ (π : PointedLocalPermutations (Fin n)) (d : Fin n → ℚ)
      (K : Submodule ℚ (Fin n → ℚ)),
      K = Submodule.span ℚ ({(fun _ => (1 : ℚ)), d} : Set (Fin n → ℚ)) →
      (∃ u v : Fin n, d u ≠ d v) →
      (∀ i : Fin n, Function.Involutive (π.1 i)) →
      (∀ i : Fin n, ∀ x : Fin n → ℚ, x ∈ K →
        permuteCoordinateVector (π.1 i) x ∈ K) →
      ∀ i : Fin n,
        (permuteCoordinateVector (π.1 i) d = d ∨
          permuteCoordinateVector (π.1 i) d = affineReflectionVector i d) ∧
          ¬ (permuteCoordinateVector (π.1 i) d = d ∧
            permuteCoordinateVector (π.1 i) d = affineReflectionVector i d)

end

end MathlibPlus.Open.ResearchFormalization.Claim17085
