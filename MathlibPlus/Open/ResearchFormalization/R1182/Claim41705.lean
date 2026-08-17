import MathlibPlus.Open.ResearchFormalization.R1182.Claim41710
import MathlibPlus.Open.ResearchFormalization.R1182.Claim41711

namespace MathlibPlus.Open.ResearchFormalization.R1182.Claim41705

open MathlibPlus.Open.ResearchFormalization.R1182.Claim41710

abbrev PrimeBlock (p : ℕ) :=
  MathlibPlus.Open.ResearchFormalization.R1182.Claim41711.PrimeBlock p

/-- The actual projected relative derivative with connection base `h` and
vertex base `k`, using the normalized relative-derivative action. -/
def projectedRelativeDerivative (p : ℕ) (orientation : Bool)
    (lam : Q12 → (ZMod p)ˣ) (tau : Q12 → ZMod p)
    (h k : Q12) : Q12 :=
  (MathlibPlus.Open.ResearchFormalization.R1182.Claim41711.affineRelativeDerivative
      p orientation lam tau
      ((0, k) : PrimeBlock p) ((0, h) : PrimeBlock p)).2

def projectedDerivativeStep (p : ℕ) (orientation : Bool)
    (lam : Q12 → (ZMod p)ˣ) (tau : Q12 → ZMod p)
    (x y : Q12) : Prop :=
  y = q12Inv x ∨ x = q12Inv y ∨
    (∃ h : Q12, y = projectedRelativeDerivative p orientation lam tau h x) ∨
    (∃ h : Q12, x = projectedRelativeDerivative p orientation lam tau h y)

def projectedDerivativeAtom (p : ℕ) (orientation : Bool)
    (lam : Q12 → (ZMod p)ˣ) (tau : Q12 → ZMod p)
    (x : Q12) : Set Q12 :=
  {y | Relation.ReflTransGen
    (projectedDerivativeStep p orientation lam tau) x y}

def projectedDerivativeAtomFamily (p : ℕ) (orientation : Bool)
    (lam : Q12 → (ZMod p)ˣ) (tau : Q12 → ZMod p)
    (T : Set Q12) : Prop :=
  completeProjectedAtom T ∧
    ∃ x : Q12, projectedDerivativeAtom p orientation lam tau x = T

def fullDerivativeStep (p : ℕ) (orientation : Bool)
    (lam : Q12 → (ZMod p)ˣ) (tau : Q12 → ZMod p)
    (x y : PrimeBlock p) : Prop :=
  (∃ g : PrimeBlock p,
    y = MathlibPlus.Open.ResearchFormalization.R1182.Claim41711.affineRelativeDerivative
      p orientation lam tau g x) ∨
  (∃ g : PrimeBlock p,
    x = MathlibPlus.Open.ResearchFormalization.R1182.Claim41711.affineRelativeDerivative
      p orientation lam tau g y) ∨
  y = MathlibPlus.Open.ResearchFormalization.R1182.Claim41711.primeBlockInv p x ∨
    x = MathlibPlus.Open.ResearchFormalization.R1182.Claim41711.primeBlockInv p y

def fullDerivativeOrbit (p : ℕ) (orientation : Bool)
    (lam : Q12 → (ZMod p)ˣ) (tau : Q12 → ZMod p)
    (x : PrimeBlock p) : Set (PrimeBlock p) :=
  {y | Relation.ReflTransGen
    (fullDerivativeStep p orientation lam tau) x y}

def topTranslation (p : ℕ) (v : ZMod p) : PrimeBlock p → PrimeBlock p :=
  fun z => (z.1 + v, z.2)

def topTranslationStep (p : ℕ) (v : ZMod p)
    (x y : PrimeBlock p) : Prop :=
  y = topTranslation p v x ∨ x = topTranslation p v y

def topTranslationOrbit (p : ℕ) (v : ZMod p)
    (x : PrimeBlock p) : Set (PrimeBlock p) :=
  {y | Relation.ReflTransGen (topTranslationStep p v) x y}

def topTranslationSaturatesFiber (p : ℕ) (v : ZMod p)
    (h : Q12) : Prop :=
  v ≠ 0 ∧
    ∀ x : ZMod p,
      topTranslationOrbit p v (x, h) =
        primeFiber p ({h} : Set Q12)

def derivativeFiberTopTranslationSaturation (p : ℕ) (orientation : Bool)
    (lam : Q12 → (ZMod p)ˣ) (tau : Q12 → ZMod p)
    (h : Q12) : Prop :=
  ∃ v : ZMod p,
    topTranslationSaturatesFiber p v h ∧
      ∀ x : ZMod p,
        topTranslationOrbit p v (x, h) ⊆
          fullDerivativeOrbit p orientation lam tau (x, h)

def nontrivialQuietVoltageAtom (p : ℕ) (orientation : Bool)
    (lam : Q12 → (ZMod p)ˣ) (tau : Q12 → ZMod p)
    (T : Set Q12) : Prop :=
  T.Nonempty ∧
    quietVoltageSolution p orientation lam tau T
      (Set.univ : Set Q12)

def q12Subgroup (U : Set Q12) : Prop :=
  q12One ∈ U ∧
    (∀ x y : Q12, x ∈ U → y ∈ U → q12Mul x y ∈ U) ∧
    (∀ x : Q12, x ∈ U → q12Inv x ∈ U)

def scalarProfileStabilizerAndFiberSaturation_claim41705 : Prop :=
  ∀ p : ℕ, Nat.Prime p → 3 < p →
    ∀ (orientation : Bool)
      (lam : Q12 → (ZMod p)ˣ) (tau : Q12 → ZMod p),
      normalizedAffineFunctions lam tau →
      let Q := scalarStabilizer p orientation lam
      q12Subgroup Q ∧
        (∀ T : Set Q12,
          projectedDerivativeAtomFamily p orientation lam tau T →
            ∀ h : Q12, h ∈ T → h ∉ Q →
              derivativeFiberTopTranslationSaturation
                p orientation lam tau h) ∧
        (∀ T : Set Q12,
          projectedDerivativeAtomFamily p orientation lam tau T →
            nontrivialQuietVoltageAtom p orientation lam tau T →
              T ⊆ Q)

end MathlibPlus.Open.ResearchFormalization.R1182.Claim41705
