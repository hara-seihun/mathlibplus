import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1182.Claim41710

abbrev Q12 := ZMod 3 × ZMod 4
abbrev PrimeBlock (p : ℕ) := ZMod p × Q12

-- The displayed semidirect-product coordinates for Q12.
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

def switch (orientation : Bool) (h : Q12) : Q12 :=
  if orientation = true then q12SigmaInv h else q12Sigma h

def switchInv (orientation : Bool) (h : Q12) : Q12 :=
  if orientation = true then q12Sigma h else q12SigmaInv h

def q12Sign (p : ℕ) (h : Q12) : ZMod p :=
  (-1 : ZMod p) ^ h.2.val

def primeBlockMul (p : ℕ) (x y : PrimeBlock p) : PrimeBlock p :=
  (x.1 + q12Sign p x.2 * y.1, q12Mul x.2 y.2)

def primeBlockInv (p : ℕ) (x : PrimeBlock p) : PrimeBlock p :=
  (-q12Sign p x.2 * x.1, q12Inv x.2)

def affineLiftMap (p : ℕ) (orientation : Bool)
    (lam : Q12 → (ZMod p)ˣ) (tau : Q12 → ZMod p)
    (z : PrimeBlock p) : PrimeBlock p :=
  (((lam z.2 : ZMod p) * z.1 + tau z.2), switch orientation z.2)

def affineLiftInvMap (p : ℕ) (orientation : Bool)
    (lam : Q12 → (ZMod p)ˣ) (tau : Q12 → ZMod p)
    (z : PrimeBlock p) : PrimeBlock p :=
  let h := switchInv orientation z.2
  (((((lam h)⁻¹ : (ZMod p)ˣ) : ZMod p) * (z.1 - tau h)), h)

def normalizedAffineFunctions {p : ℕ} (lam : Q12 → (ZMod p)ˣ)
    (tau : Q12 → ZMod p) : Prop :=
  lam q12One = 1 ∧ tau q12One = 0

def scalarProfile (p : ℕ) (orientation : Bool)
    (lam : Q12 → (ZMod p)ˣ) (k : Q12) : ZMod p :=
  (lam k : ZMod p) * q12Sign p k *
    (q12Sign p (switch orientation k))⁻¹

def scalarStabilizer (p : ℕ) (orientation : Bool)
    (lam : Q12 → (ZMod p)ˣ) : Set Q12 :=
  {h | ∀ k : Q12,
    scalarProfile p orientation lam (q12Mul h k) =
      scalarProfile p orientation lam k}

def relativeCoefficient (p : ℕ) (orientation : Bool)
    (lam : Q12 → (ZMod p)ˣ) (h k : Q12) : ZMod p :=
  (lam (q12Mul h k) : ZMod p) * q12Sign p h -
    q12Sign p (switch orientation (q12Mul h k)) *
      (q12Sign p (switch orientation k))⁻¹ * (lam k : ZMod p)

def quietVoltageSolution (p : ℕ) (orientation : Bool)
    (lam : Q12 → (ZMod p)ˣ) (tau : Q12 → ZMod p)
    (connectionBases vertexBases : Set Q12) : Prop :=
  tau q12One = 0 ∧
    ∀ h : Q12, h ∈ connectionBases →
      ∀ k : Q12, k ∈ vertexBases →
        relativeCoefficient p orientation lam h k = 0 ∧
          tau (q12Mul h k) =
            tau h + q12Sign p h * tau k

def c4Carrier : Set Q12 :=
  {h | h.1 = 0}

def axisAtom : Set Q12 :=
  {h | h.1 = 0 ∧ h ≠ q12One}

def outerAtom : Set Q12 :=
  {h | h.1 ≠ 0}

def completeProjectedAtom (T : Set Q12) : Prop :=
  T = ({q12One} : Set Q12) ∨ T = axisAtom ∨ T = outerAtom

def quietFamily (i : Fin 3) : Set Q12 :=
  match i.1 with
  | 0 => axisAtom
  | 1 => outerAtom
  | _ => axisAtom ∪ outerAtom

def isGroupAutomorphism (p : ℕ)
    (f : PrimeBlock p → PrimeBlock p) : Prop :=
  Function.Bijective f ∧
    ∀ x y : PrimeBlock p,
      f (primeBlockMul p x y) =
        primeBlockMul p (f x) (f y)

def alpha (p : ℕ) (c : ZMod p) : PrimeBlock p → PrimeBlock p :=
  fun z => (z.1 + c * (1 - q12Sign p z.2), z.2)

def primeFiber (p : ℕ) (T : Set Q12) : Set (PrimeBlock p) :=
  {z | z.2 ∈ T}

def affineAtomShadow (p : ℕ) (orientation : Bool)
    (lam : Q12 → (ZMod p)ˣ) (tau : Q12 → ZMod p)
    (c : ZMod p) (vertexBases : Set Q12) : Prop :=
  isGroupAutomorphism p (alpha p c) ∧
    (∀ h : Q12, h ∈ vertexBases →
      tau h = c * (1 - q12Sign p h)) ∧
    (∀ T : Set Q12, completeProjectedAtom T →
      Set.image (affineLiftMap p orientation lam tau) (primeFiber p T) =
        Set.image (alpha p c) (primeFiber p T))

def claim41710 : Prop :=
  ∀ p : ℕ, Nat.Prime p → 3 < p →
    ∀ (orientation : Bool)
      (lam : Q12 → (ZMod p)ˣ) (tau : Q12 → ZMod p),
      normalizedAffineFunctions lam tau →
      let Q := scalarStabilizer p orientation lam
      (Q ≠ c4Carrier → Q ≠ (Set.univ : Set Q12) →
        affineAtomShadow p orientation lam tau 0 (∅ : Set Q12)) ∧
      (Q = c4Carrier →
        quietVoltageSolution p orientation lam tau axisAtom c4Carrier →
          ∃ c : ZMod p,
            affineAtomShadow p orientation lam tau c c4Carrier) ∧
      (Q = (Set.univ : Set Q12) →
        ∀ J : Finset (Fin 3),
          (∀ i : Fin 3, i ∈ J →
            quietVoltageSolution p orientation lam tau
              (quietFamily i) (Set.univ : Set Q12)) →
          ∃ c : ZMod p,
            ∀ i : Fin 3, i ∈ J →
              affineAtomShadow p orientation lam tau c
                (Set.univ : Set Q12))

end MathlibPlus.Open.ResearchFormalization.R1182.Claim41710
