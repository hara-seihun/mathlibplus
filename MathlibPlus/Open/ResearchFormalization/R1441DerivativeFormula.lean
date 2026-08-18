import Mathlib
import MathlibPlus.Open.ResearchFormalization.R1441MarkedOffsetTransport

namespace MathlibPlus.Open.ResearchFormalization.R1441DerivativeFormula

noncomputable section

open MathlibPlus.Open.ResearchFormalization.R1441MarkedOffsetTransport

/-- The matching scalar attached to a quotient row. -/
def chi (h : H) : ZMod 7 :=
  (2 : ZMod 7) ^ h.2.val

/-- Inversion in the displayed matching-scalar base carrier. -/
def hInv (h : H) : H :=
  (-(chi h)⁻¹ * h.1, -h.2)

/-- Scalar multiplication on the two-coordinate fibre. -/
def wScale (a : ZMod 7) (w : W) : W :=
  (a * w.1, a * w.2)

/-- The matching-scalar product on the supplied fibre/base carrier. -/
def matchingProduct (g g' : W × H) : W × H :=
  (g.1 + hScalar g.2 g'.1, hMul g.2 g'.2)

/-- The displayed inverse operation for the matching-scalar product. -/
def matchingInverse (g : W × H) : W × H :=
  (wScale (-(chi g.2)⁻¹) g.1, hInv g.2)

/-- The quotient-identity action associated with a family of row
permutations. -/
def quotientIdentityAction (F : H → Equiv.Perm W) (g : W × H) : W × H :=
  (F g.2 g.1, g.2)

/-- Its direct rowwise inverse action. -/
def quotientIdentityActionInv (F : H → Equiv.Perm W)
    (g : W × H) : W × H :=
  ((F g.2).symm g.1, g.2)

/-- The normalized relative derivative obtained from the quotient-identity
action and the matching-scalar product, before its displayed coordinate
formula is asserted. -/
def normalizedRelativeDerivativeFromAction
    (F : H → Equiv.Perm W) (h k : H) (x w : W) : W :=
  (quotientIdentityActionInv F
    (matchingProduct
      (quotientIdentityAction F (matchingProduct (w, h) (x, k)))
      (matchingInverse (quotientIdentityAction F (x, k))))).1

/-- Claim 37232: the exact normalized relative derivative in quotient row
`h`, indexed by `(k,x)`, has the displayed formula for every arbitrary
family of row permutations normalized at the identity row. -/
def claim37232_exactDerivativeFormula : Prop :=
  ∀ (F : H → Equiv.Perm W),
    F (0, 0) = Equiv.refl W →
      ∀ h k : H, ∀ x w : W,
        normalizedRelativeDerivativeFromAction F h k x w =
          (F h).symm
            (F (hMul h k) (w + hScalar h x) -
              hScalar h (F k x))

end

end MathlibPlus.Open.ResearchFormalization.R1441DerivativeFormula
