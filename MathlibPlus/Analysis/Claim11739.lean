import Mathlib

namespace MathlibPlus.Analysis.Claim11739

/-- The exact product of the two displayed first/second-order jets.  The four
summands make the unique total-degree-two term and the two vanishing axes
explicit; commutativity records invariance of that leading coefficient under
swapping the two sides. -/
theorem lowestBivariateProduct {R : Type*} [CommRing R]
    (eL eR vL vR wL wR : R) :
    let P : R → R → R := fun u v =>
      (u * vL + u ^ 2 * wL) * (v * vR + v ^ 2 * wR)
    P eL eR =
        eL * eR * (vL * vR)
          + eL ^ 2 * eR * (wL * vR)
          + eL * eR ^ 2 * (vL * wR)
          + eL ^ 2 * eR ^ 2 * (wL * wR) ∧
      P 0 eR = 0 ∧
      P eL 0 = 0 ∧
      vL * vR = vR * vL := by
  dsimp
  refine ⟨?_, ?_, ?_, ?_⟩
  · ring
  · ring
  · ring
  · ring

end MathlibPlus.Analysis.Claim11739
