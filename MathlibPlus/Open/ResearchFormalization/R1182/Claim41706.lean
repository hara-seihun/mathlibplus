import MathlibPlus.Open.ResearchFormalization.R1182.Claim31941

namespace MathlibPlus.Open.ResearchFormalization.R1182.Claim41706

open MathlibPlus.Open.ResearchFormalization.R1182.Claim31941

abbrev Gp (p : ℕ) := ZMod p × Q12

def gpMultiply (p : ℕ) (x y : Gp p) : Gp p :=
  (x.1 + q12Sign p x.2 * y.1, q12Mul x.2 y.2)

def gpInverse (p : ℕ) (x : Gp p) : Gp p :=
  (-(q12Sign p x.2)⁻¹ * x.1, q12Inv x.2)

def gpRelativeDerivative (p : ℕ) (lam : Q12 → (ZMod p)ˣ)
    (tau : Q12 → ZMod p) (h : Q12) : Gp p → Gp p :=
  fun z =>
    gpMultiply p
      (affineLift p lam tau
        (gpMultiply p ((0, h) : Gp p) z))
      (gpInverse p (affineLift p lam tau z))

def projectedDerivative (p : ℕ) (lam : Q12 → (ZMod p)ˣ)
    (tau : Q12 → ZMod p) (h k : Q12) : Q12 :=
  q12SigmaInv
    ((gpRelativeDerivative p lam tau h ((0, k) : Gp p)).2)

def projectedDerivativePoint (p : ℕ) (lam : Q12 → (ZMod p)ˣ)
    (tau : Q12 → ZMod p) (h : Q12) (x : ZMod p) (k : Q12) : ZMod p × Q12 :=
  ((gpRelativeDerivative p lam tau h (x, k)).1,
    q12SigmaInv ((gpRelativeDerivative p lam tau h (x, k)).2))

def projectedDerivativeInversionAtom (p : ℕ)
    (lam : Q12 → (ZMod p)ˣ) (tau : Q12 → ZMod p) (h : Q12) : Set Q12 :=
  {q | (∃ k : Q12, q = projectedDerivative p lam tau h k) ∨
    (∃ k : Q12,
      q = q12Inv (projectedDerivative p lam tau h k))}

def projectedAtomFamily (p : ℕ) (lam : Q12 → (ZMod p)ˣ)
    (tau : Q12 → ZMod p) : Set (Set Q12) :=
  {S | ∃ h : Q12, S = projectedDerivativeInversionAtom p lam tau h}

def expectedProjectedAtomFamily : Set (Set Q12) :=
  {S | S = ({q12One} : Set Q12) ∨ S = axisAtom ∨ S = outerAtom}

def c4Subgroup : Set Q12 :=
  {h | h.1 = 0}

def q12Subgroup (U : Set Q12) : Prop :=
  q12One ∈ U ∧
    (∀ x : Q12, x ∈ U → q12Inv x ∈ U) ∧
    (∀ x y : Q12, x ∈ U → y ∈ U → q12Mul x y ∈ U)

def atomActive (U atom : Set Q12) : Prop :=
  ∃ h : Q12, h ∈ atom ∧ h ∉ U

def projectedFiberImage (p : ℕ) (lam : Q12 → (ZMod p)ˣ)
    (tau : Q12 → ZMod p) (h q : Q12) : Set (ZMod p) :=
  {y | ∃ x : ZMod p, ∃ k : Q12,
    projectedDerivativePoint p lam tau h x k = (y, q)}

def topVariationCoefficient (p : ℕ) (lam : Q12 → (ZMod p)ˣ)
    (tau : Q12 → ZMod p) (h k : Q12) : ZMod p :=
  (gpRelativeDerivative p lam tau h (1, k)).1 -
    (gpRelativeDerivative p lam tau h (0, k)).1

def nonzeroTopTranslation (p : ℕ) (lam : Q12 → (ZMod p)ˣ)
    (tau : Q12 → ZMod p) (h : Q12) : Prop :=
  ∃ k : Q12, topVariationCoefficient p lam tau h k ≠ 0

def fiberSaturatedAt (p : ℕ) (lam : Q12 → (ZMod p)ˣ)
    (tau : Q12 → ZMod p) (h q : Q12) : Prop :=
  ∀ y : ZMod p,
    y ∈ projectedFiberImage p lam tau h q ∨
      y ∈ projectedFiberImage p lam tau h (q12Inv q)

def atomFiberSaturated (p : ℕ) (lam : Q12 → (ZMod p)ˣ)
    (tau : Q12 → ZMod p) (U atom : Set Q12) : Prop :=
  ∀ h : Q12, h ∈ atom → h ∉ U →
    nonzeroTopTranslation p lam tau h ∧
      ∀ q : Q12, q ∈ projectedDerivativeInversionAtom p lam tau h →
        fiberSaturatedAt p lam tau h q

def completeAtomSubgroupClassification : Prop :=
  q12Subgroup c4Subgroup ∧
    q12Subgroup (Set.univ : Set Q12) ∧
    axisAtom ⊆ c4Subgroup ∧
    axisAtom ⊆ (Set.univ : Set Q12) ∧
    outerAtom ⊆ (Set.univ : Set Q12) ∧
    (∀ U : Set Q12, q12Subgroup U →
      (axisAtom ⊆ U → U = c4Subgroup ∨ U = (Set.univ : Set Q12)) ∧
      (outerAtom ⊆ U → U = (Set.univ : Set Q12)))

def projectedAtomAndSubgroupClassification_claim41706 : Prop :=
  completeAtomSubgroupClassification ∧
    (∀ p : ℕ, Nat.Prime p → 3 < p →
      ∀ (lam : Q12 → (ZMod p)ˣ) (tau : Q12 → ZMod p),
        normalizedAffineFunctions lam tau →
          projectedAtomFamily p lam tau = expectedProjectedAtomFamily ∧
          (∀ h : Q12,
            h = q12One →
              projectedDerivativeInversionAtom p lam tau h =
                ({q12One} : Set Q12)) ∧
          (∀ h : Q12,
            h ∈ axisAtom →
              projectedDerivativeInversionAtom p lam tau h = axisAtom) ∧
          (∀ h : Q12,
            h ∈ outerAtom →
              projectedDerivativeInversionAtom p lam tau h = outerAtom) ∧
          Set.ncard ({q12One} : Set Q12) = 1 ∧
          Set.ncard axisAtom = 3 ∧
          Set.ncard outerAtom = 8 ∧
          (∀ U : Set Q12,
            U = scalarStabilizer p lam →
              U ≠ c4Subgroup → U ≠ (Set.univ : Set Q12) →
                atomActive U axisAtom ∧
                  atomActive U outerAtom ∧
                  atomFiberSaturated p lam tau U axisAtom ∧
                  atomFiberSaturated p lam tau U outerAtom))

end MathlibPlus.Open.ResearchFormalization.R1182.Claim41706
