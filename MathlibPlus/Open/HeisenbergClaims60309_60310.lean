import Mathlib

namespace MathlibPlus.Open

namespace Heisenberg

structure Element (p : ℕ) where
  a : ZMod p
  b : ZMod p
  c : ZMod p

abbrev Omega (p : ℕ) := ZMod p × ZMod p

def one (p : ℕ) : Element p :=
  ⟨0, 0, 0⟩

def mul {p : ℕ} (x y : Element p) : Element p :=
  ⟨x.a + y.a, x.b + y.b, x.c + y.c + x.a * y.b⟩

def inv {p : ℕ} (x : Element p) : Element p :=
  ⟨-x.a, -x.b, -x.c + x.a * x.b⟩

def heisPow {p : ℕ} (x : Element p) : ℕ → Element p
  | 0 => one p
  | n + 1 => mul (heisPow x n) x

def U (p : ℕ) : Set (Element p) :=
  {x | x.b = 0 ∧ x.c = 0}

def coordinate {p : ℕ} (x : Element p) : Omega p :=
  (x.b, x.c)

def action {p : ℕ} (g : Element p) (ω : Omega p) : Omega p :=
  (ω.1 + g.b, ω.2 + g.c + g.a * ω.1)

def leftCosetEquivalent (p : ℕ) (x y : Element p) : Prop :=
  ∃ u, u ∈ U p ∧ y = mul x u

def heisenbergGroupAxioms (p : ℕ) : Prop :=
  (∀ x y z : Element p, mul (mul x y) z = mul x (mul y z)) ∧
    (∀ x : Element p, mul (one p) x = x ∧ mul x (one p) = x) ∧
    (∀ x : Element p, mul (inv x) x = one p ∧ mul x (inv x) = one p)

def isSubgroup (p : ℕ) (S : Set (Element p)) : Prop :=
  (one p ∈ S) ∧
    (∀ x, x ∈ S → ∀ y, y ∈ S → mul x y ∈ S) ∧
    (∀ x, x ∈ S → inv x ∈ S)

def identifiesLeftCosets (p : ℕ) : Prop :=
  (∀ x y : Element p,
      leftCosetEquivalent p x y ↔ coordinate x = coordinate y) ∧
    Function.Surjective (coordinate (p := p))

def isPermutationAction (p : ℕ) : Prop :=
  (∀ g : Element p, Function.Bijective (action g)) ∧
    (∀ ω : Omega p, action (one p) ω = ω) ∧
    (∀ g h : Element p, ∀ ω : Omega p,
      action (mul g h) ω = action g (action h ω))

def isTransitive (p : ℕ) : Prop :=
  ∀ ω ω' : Omega p, ∃ g : Element p, action g ω = ω'

def hasDegree (p n : ℕ) : Prop :=
  Nonempty (Omega p ≃ Fin n)

def claim60309 : Prop :=
  ∀ p : ℕ, Nat.Prime p → Odd p →
    heisenbergGroupAxioms p ∧
      isSubgroup p (U p) ∧
        identifiesLeftCosets p ∧
          isPermutationAction p ∧
            isTransitive p ∧
              hasDegree p (p ^ 2)

def hasOrder (p : ℕ) (S : Set (Element p)) (n : ℕ) : Prop :=
  Nonempty (Subtype (fun x : Element p => x ∈ S) ≃ Fin n)

def isElementaryAbelian (p : ℕ) (S : Set (Element p)) : Prop :=
  isSubgroup p S ∧
    (∀ x, x ∈ S → ∀ y, y ∈ S → mul x y = mul y x) ∧
      (∀ x, x ∈ S → heisPow x p = one p) ∧
        hasOrder p S (p ^ 2)

def E (p : ℕ) (m : ZMod p) : Set (Element p) :=
  {x | ∃ a c : ZMod p, x = ⟨a, m * a, c⟩}

def EInfinity (p : ℕ) : Set (Element p) :=
  {x | ∃ b c : ZMod p, x = ⟨0, b, c⟩}

def trivialIntersection (p : ℕ) (S : Set (Element p)) : Prop :=
  ∀ x, (x ∈ S ∧ x ∈ U p) ↔ x = one p

def regularOnOmega (p : ℕ) (S : Set (Element p)) : Prop :=
  ∀ ω ω' : Omega p, ∃! g, g ∈ S ∧ action g ω = ω'

def isNormal (p : ℕ) (S : Set (Element p)) : Prop :=
  ∀ g x : Element p, x ∈ S → mul (mul g x) (inv g) ∈ S

def conjugate (p : ℕ) (g : Element p) (S : Set (Element p)) : Set (Element p) :=
  {x | ∃ s, s ∈ S ∧ x = mul (mul g s) (inv g)}

def notConjugate (p : ℕ) (S T : Set (Element p)) : Prop :=
  ¬ ∃ g : Element p, conjugate p g S = T

def claim60310 : Prop :=
  ∀ p : ℕ, Nat.Prime p → Odd p →
    heisenbergGroupAxioms p ∧
      (∀ m : ZMod p, isElementaryAbelian p (E p m)) ∧
        isElementaryAbelian p (EInfinity p) ∧
          (∀ m : ZMod p, m ≠ 0 →
            trivialIntersection p (E p m) ∧
              regularOnOmega p (E p m)) ∧
            trivialIntersection p (EInfinity p) ∧
              regularOnOmega p (EInfinity p) ∧
                let R : Set (Element p) := E p 1
                let T : Set (Element p) := EInfinity p
                R ≠ T ∧
                  isElementaryAbelian p R ∧
                    regularOnOmega p R ∧
                      isElementaryAbelian p T ∧
                        regularOnOmega p T ∧
                          isNormal p R ∧
                            isNormal p T ∧
                              notConjugate p R T

end Heisenberg

end MathlibPlus.Open
