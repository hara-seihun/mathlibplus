import Mathlib
import MathlibPlus.Open.ResearchFormalization.R1245Claim30547

namespace MathlibPlus.Open.ResearchFormalization.R1245Claim30541

noncomputable section

open MathlibPlus.Open.ResearchFormalization.R1245Claim30547

private def groupAutomorphism30541 {n : ℕ}
    (α : Equiv.Perm (Q4n n)) : Prop :=
  ∀ x y : Q4n n,
    α (fourLayerMul x y) =
      fourLayerMul (α x) (α y)

/-- Claim 30541: on the exact odd square-free four-layer group, every
normalized inverse-closed relative-derivative-invariant connection set is
carried to its normalized affine image by one actual group automorphism. -/
def claim30541_normalizedDerivativeCIConclusion : Prop :=
  ∀ (n : ℕ),
    oddSquarefreeNat n →
      ∀ (lambdas : Fin 4 → (Cn n)ˣ) (τ : Fin 4 → Cn n)
        (π : Equiv.Perm (Fin 4)) (f : Equiv.Perm (Q4n n))
        (S : Set (Q4n n)),
        normalizedBlockAffine lambdas τ π f →
          identityFree S ∧
            inverseClosed S ∧
              relativeDerivativeInvariant f S →
                ∃ α : Equiv.Perm (Q4n n),
                  groupAutomorphism30541 α ∧
                    Set.image α S = Set.image f S

end

end MathlibPlus.Open.ResearchFormalization.R1245Claim30541
