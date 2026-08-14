import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch

abbrev H (p m : ℕ) := Fin m → ZMod p

def normalizedScalar {p m : ℕ} (u : H p m → ZMod p) : Prop :=
  u 0 = 0

def normalizedPermutation {p m : ℕ} (g : H p m ≃ H p m) : Prop :=
  g 0 = 0

def relativeMap {p m : ℕ} (g : H p m ≃ H p m) (k h : H p m) : H p m :=
  g.symm (g (h + k) - g k)

def voltage {p m : ℕ} (g : H p m ≃ H p m) (s : H p m → ZMod p)
    (k h : H p m) : ZMod p :=
  s (h + k) - s k - s (relativeMap g k h)

def quietPotential {p m : ℕ} (g : H p m ≃ H p m) (s t : H p m → ZMod p) : Prop :=
  normalizedScalar t ∧
    ∀ k h, voltage g s k h = t (relativeMap g k h) - t h

def switchingIdentity {p m : ℕ} (g : H p m ≃ H p m)
    (s a b : H p m → ZMod p) : Prop :=
  ∀ x y, s x - s y = a (x - y) + b (g x - g y)

/-- Claim 37410: a normalized quiet potential gives the stated switching data. -/
def claim37410 : Prop :=
  ∀ (p m : ℕ), Nat.Prime p →
    ∀ (g : H p m ≃ H p m) (s t : H p m → ZMod p),
      normalizedPermutation g →
      normalizedScalar s →
      quietPotential g s t →
      let a : H p m → ZMod p := fun x => -t x
      let b : H p m → ZMod p := fun y => s (g.symm y) + t (g.symm y)
      normalizedScalar a ∧
        normalizedScalar b ∧
        ∀ x y, s x - s y = a (x - y) + b (g x - g y)

/-- Claim 37411: normalized switching data gives the stated quiet potential. -/
def claim37411 : Prop :=
  ∀ (p m : ℕ), Nat.Prime p →
    ∀ (g : H p m ≃ H p m) (s a b : H p m → ZMod p),
      normalizedPermutation g →
      normalizedScalar s →
      normalizedScalar a →
      normalizedScalar b →
      switchingIdentity g s a b →
      let t : H p m → ZMod p := fun h => -a h
      quietPotential g s t ∧
        ∀ k h,
          voltage g s k h = a h - a (relativeMap g k h) ∧
          voltage g s k h = t (relativeMap g k h) - t h

def signedCoordinate (e : ZMod 3) : Prop :=
  e = 1 ∨ e = -1

def signedParameters (ε τ : Fin 35 → ZMod 3) : Prop :=
  (∀ n, signedCoordinate (ε n)) ∧ τ 0 = 0

abbrev BlockPoint := ZMod 3 × Fin 35

def blockPreserving (f : BlockPoint ≃ BlockPoint) : Prop :=
  ∀ (i : ZMod 3) (n : Fin 35), (f (i, n)).2 = n

def identityFixing (f : BlockPoint ≃ BlockPoint) : Prop :=
  f (0, 0) = (0, 0)

def normalizedBlockChart (f : BlockPoint ≃ BlockPoint) : Prop :=
  blockPreserving f ∧ identityFixing f

def chartFormula (f : BlockPoint ≃ BlockPoint)
    (ε τ : Fin 35 → ZMod 3) : Prop :=
  ∀ (i : ZMod 3) (n : Fin 35),
    f (i, n) = (ε n * i + τ n, n)

/-- Claim 37519: the complete normalized blockwise chart normal form and count. -/
def claim37519 : Prop :=
  (∀ (f : BlockPoint ≃ BlockPoint), normalizedBlockChart f →
    ∃! p : (Fin 35 → ZMod 3) × (Fin 35 → ZMod 3),
      signedParameters p.1 p.2 ∧ chartFormula f p.1 p.2) ∧
  (∀ (ε τ : Fin 35 → ZMod 3), signedParameters ε τ →
    ∃! f : BlockPoint ≃ BlockPoint,
      normalizedBlockChart f ∧ chartFormula f ε τ) ∧
  (letI : Fintype {f : BlockPoint ≃ BlockPoint // normalizedBlockChart f} :=
      Fintype.ofFinite _;
    Fintype.card {f : BlockPoint ≃ BlockPoint // normalizedBlockChart f} = 2 * 6 ^ 34)

end MathlibPlus.Open.ResearchFormalizationBatch
