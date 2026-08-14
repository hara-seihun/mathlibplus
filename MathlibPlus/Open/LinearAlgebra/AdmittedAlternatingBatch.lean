import Mathlib

namespace MathlibPlus.Open.LinearAlgebra

noncomputable section

/-- The endpoint wedge attached to a quotient map on physical endpoint states. -/
def endpointWedge {P X : Type*} (q : P → X) (a b : P) :
    ⋀[ℚ]^2 (X →₀ ℚ) :=
  exteriorPower.ιMulti ℚ 2
    ![Finsupp.single (q a) 1, Finsupp.single (q b) 1]

/--
Claim 53873.  For every alternating endpoint kernel, the endpoint wedge has
its universal factorization through the second exterior power.  The response
on a closed four-cycle is included in the same declaration, with the exact
opposite-endpoint identification from the claim.
-/
def claim53873_exteriorSquareUniversality : Prop :=
  ∀ {P X Z : Type*} [AddCommGroup Z] [Module ℚ Z]
    (q : P → X) (φ : X → X → Z),
    (∀ x, φ x x = 0) →
    (∀ x y, φ x y = -φ y x) →
    ∃! L : (⋀[ℚ]^2 (X →₀ ℚ)) →ₗ[ℚ] Z,
      (∀ x y,
        L (exteriorPower.ιMulti ℚ 2
          ![Finsupp.single x 1, Finsupp.single y 1]) = φ x y) ∧
      (∀ a b,
        L (endpointWedge q a b) = φ (q a) (q b)) ∧
      (∀ a b d c, q a = q d →
        L (endpointWedge q a b) + L (endpointWedge q b d) +
          L (endpointWedge q d c) + L (endpointWedge q c a) = 0)

end

end MathlibPlus.Open.LinearAlgebra
