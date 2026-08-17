import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1182.Claim41711

abbrev Q12 := ZMod 3 × ZMod 4
abbrev PrimeBlock (p : ℕ) := ZMod p × Q12

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

def affineRelativeDerivative (p : ℕ) (orientation : Bool)
    (lam : Q12 → (ZMod p)ˣ) (tau : Q12 → ZMod p)
    (g z : PrimeBlock p) : PrimeBlock p :=
  affineLiftInvMap p orientation lam tau
    (primeBlockMul p
      (affineLiftMap p orientation lam tau (primeBlockMul p z g))
      (primeBlockInv p (affineLiftMap p orientation lam tau g)))

def derivativeInvariant (p : ℕ) (orientation : Bool)
    (lam : Q12 → (ZMod p)ˣ) (tau : Q12 → ZMod p)
    (S : Set (PrimeBlock p)) : Prop :=
  ∀ g : PrimeBlock p,
    Set.image (affineRelativeDerivative p orientation lam tau g) S = S

def inverseClosed (p : ℕ) (S : Set (PrimeBlock p)) : Prop :=
  ∀ z : PrimeBlock p,
    z ∈ S ↔ primeBlockInv p z ∈ S

def isGroupAutomorphism (p : ℕ)
    (f : PrimeBlock p → PrimeBlock p) : Prop :=
  Function.Bijective f ∧
    ∀ x y : PrimeBlock p,
      f (primeBlockMul p x y) =
        primeBlockMul p (f x) (f y)

def alpha (p : ℕ) (c : ZMod p) : PrimeBlock p → PrimeBlock p :=
  fun z => (z.1 + c * (1 - q12Sign p z.2), z.2)

def claim41711 : Prop :=
  ∀ p : ℕ, Nat.Prime p → 3 < p →
    ∀ (orientation : Bool)
      (lam : Q12 → (ZMod p)ˣ) (tau : Q12 → ZMod p),
      normalizedAffineFunctions lam tau →
      ∀ S : Set (PrimeBlock p),
        inverseClosed p S →
          derivativeInvariant p orientation lam tau S →
            ∃ c : ZMod p,
              isGroupAutomorphism p (alpha p c) ∧
                Set.image (alpha p c) S =
                  Set.image (affineLiftMap p orientation lam tau) S

end MathlibPlus.Open.ResearchFormalization.R1182.Claim41711
