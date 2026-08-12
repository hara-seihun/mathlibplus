import Mathlib

namespace MathlibPlus.Algebra.Claim52762

/-!
Formalization of the two scalar statements in admitted claim 52762 (R-4768
S3).  The nested restriction uses the canonical subtype inclusion
`U → T`; the scalar theorem makes the nonzero denominators implicit in the
word "normalized" explicit.
-/

/-- Restricting a response on `S` first to `T` and then to `U` agrees with its
single restriction to `U`, when `U ⊆ T ⊆ S`. -/
theorem nestedRestriction
    {α β : Type*} {S T U : Set α}
    (_hU : U.Nonempty) (hUT : U ⊆ T) (hTS : T ⊆ S) (u : S → β) :
    (fun x : U =>
        (fun y : T => u ⟨y.1, hTS y.2⟩) ⟨x.1, hUT x.2⟩) =
      (fun x : U => u ⟨x.1, hTS (hUT x.2)⟩) := by
  funext x
  rfl

/-- Scalar normalization factors compose associatively. -/
theorem normalizedWeightTransfer (lambdaE lambdaT lambdaU : ℝ)
    (hT : lambdaT ≠ 0) (hU : lambdaU ≠ 0) :
    (lambdaE / lambdaT) * (lambdaT / lambdaU) = lambdaE / lambdaU := by
  field_simp

end MathlibPlus.Algebra.Claim52762
