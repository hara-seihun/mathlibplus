import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1182.Claim31941

abbrev Q12 := ZMod 3 × ZMod 4

def q12Parity (i : ZMod 4) : ZMod 3 :=
  (-1 : ZMod 3) ^ i.val

def q12Mul (x y : Q12) : Q12 :=
  (x.1 + q12Parity x.2 * y.1, x.2 + y.2)

def q12One : Q12 := (0, 0)

def q12Inv (x : Q12) : Q12 :=
  (-q12Parity x.2 * x.1, -x.2)

def q12Sigma (x : Q12) : Q12 :=
  if x = ((1, 1) : Q12) then (1, 3)
  else if x = ((1, 3) : Q12) then (2, 2)
  else if x = ((2, 2) : Q12) then (1, 1)
  else if x = ((2, 1) : Q12) then (1, 2)
  else if x = ((1, 2) : Q12) then (2, 3)
  else if x = ((2, 3) : Q12) then (2, 1)
  else x

def q12SigmaInv (x : Q12) : Q12 :=
  if x = ((1, 1) : Q12) then (2, 2)
  else if x = ((1, 3) : Q12) then (1, 1)
  else if x = ((2, 2) : Q12) then (1, 3)
  else if x = ((2, 1) : Q12) then (2, 3)
  else if x = ((1, 2) : Q12) then (2, 1)
  else if x = ((2, 3) : Q12) then (1, 2)
  else x

def q12Sign (p : ℕ) (h : Q12) : ZMod p :=
  (-1 : ZMod p) ^ h.2.val

def affineLift (p : ℕ) (lam : Q12 → (ZMod p)ˣ)
    (tau : Q12 → ZMod p) : ZMod p × Q12 → ZMod p × Q12 :=
  fun z =>
    (((lam z.2 : ZMod p) * z.1 + tau z.2), q12Sigma z.2)

def normalizedAffineFunctions {p : ℕ} (lam : Q12 → (ZMod p)ˣ)
    (tau : Q12 → ZMod p) : Prop :=
  lam q12One = 1 ∧ tau q12One = 0

def relativeCoefficient (p : ℕ) (lam : Q12 → (ZMod p)ˣ)
    (h k : Q12) : ZMod p :=
  (lam (q12Mul h k) : ZMod p) * q12Sign p h -
    q12Sign p (q12Sigma (q12Mul h k)) *
        (q12Sign p (q12Sigma k))⁻¹ * (lam k : ZMod p)

def scalarProfile (p : ℕ) (lam : Q12 → (ZMod p)ˣ) (k : Q12) : ZMod p :=
  (lam k : ZMod p) * q12Sign p k * (q12Sign p (q12Sigma k))⁻¹

def scalarStabilizer (p : ℕ) (lam : Q12 → (ZMod p)ˣ) : Set Q12 :=
  {h | ∀ k : Q12, scalarProfile p lam (q12Mul h k) = scalarProfile p lam k}

def axisAtom : Set Q12 :=
  {h | h.1 = 0 ∧ h ≠ q12One}

def outerAtom : Set Q12 :=
  {h | h.1 ≠ 0}

def completeAtomUnion (S : Set Q12) : Prop :=
  S ⊆ axisAtom ∪ outerAtom ∧
    (∀ h : Q12, h ∈ axisAtom →
      (h ∈ S ↔ ∀ h' : Q12, h' ∈ axisAtom → h' ∈ S)) ∧
    (∀ h : Q12, h ∈ outerAtom →
      (h ∈ S ↔ ∀ h' : Q12, h' ∈ outerAtom → h' ∈ S))

def quietProjectedFamily (p : ℕ) (lam : Q12 → (ZMod p)ˣ)
    (S : Set Q12) : Prop :=
  S.Nonempty ∧ completeAtomUnion S ∧
    ∀ h : Q12, h ∈ S → ∀ k : Q12,
      relativeCoefficient p lam h k = 0

def claim31941 : Prop :=
  ∀ p : ℕ, Nat.Prime p → 3 < p →
    ∀ (lam : Q12 → (ZMod p)ˣ) (tau : Q12 → ZMod p),
      normalizedAffineFunctions lam tau →
        scalarStabilizer p lam = Set.univ →
          (∀ h : Q12,
            (lam h : ZMod p) =
              q12Sign p (q12Sigma h) * (q12Sign p h)⁻¹) ∧
          (∀ S : Set Q12,
            quietProjectedFamily p lam S ↔
              S = axisAtom ∨ S = outerAtom ∨
                S = axisAtom ∪ outerAtom)

end MathlibPlus.Open.ResearchFormalization.R1182.Claim31941
