import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Research.R1542

noncomputable section

abbrev W (p : ℕ) := Fin 3 → ZMod p
abbrev H (p : ℕ) := ZMod p × ZMod 3
abbrev G (p : ℕ) := W p × H p
abbrev V (p : ℕ) := Fin 4 → ZMod p

def omegaPower {p : ℕ} (ω : ZMod p) (i : ZMod 3) : ZMod p :=
  ω ^ i.val

def hMul {p : ℕ} (ω : ZMod p) (x y : H p) : H p :=
  (x.1 + omegaPower ω x.2 * y.1, x.2 + y.2)

def hInv {p : ℕ} (ω : ZMod p) (x : H p) : H p :=
  (-(omegaPower ω (-x.2)) * x.1, -x.2)

def hZero {p : ℕ} : H p := (0, 0)

def gMul {p : ℕ} (ω : ZMod p) (x y : G p) : G p :=
  (x.1 + omegaPower ω x.2.2 • y.1, hMul ω x.2 y.2)

def gInv {p : ℕ} (ω : ZMod p) (x : G p) : G p :=
  (-(omegaPower ω (-x.2.2)) • x.1, hInv ω x.2)

def gZero {p : ℕ} : G p := (0, hZero)

def scalarCubeRoot {p : ℕ} (ω : ZMod p) : Prop :=
  ω ≠ 1 ∧ ω ^ 3 = 1

def d {p : ℕ} (ω : ZMod p) : ZMod p :=
  1 - ω

def slopeValue {p : ℕ} (t : Fin 5) : ZMod p :=
  t.val

def hSlope {p : ℕ} (ω : ZMod p) (t : Fin 5) : H p :=
  (d ω * slopeValue t, 1)

def nSlope {p : ℕ} (t : Fin 5) : W p :=
  ![1, slopeValue t, (slopeValue t) ^ 2]

def dot3 {p : ℕ} (x y : W p) : ZMod p :=
  ∑ i, x i * y i

def tau {p : ℕ} (h : H p) : W p :=
  ![h.1 ^ 4, -4 * h.1 ^ 3, 6 * h.1 ^ 2]

def gauge {p : ℕ} (g : G p) : G p :=
  (g.1 + tau g.2, g.2)

def plane {p : ℕ} (t : Fin 5) : Set (W p) :=
  {w | dot3 (nSlope t) w = 0}

def basis {p : ℕ} (i : Fin 3) : W p :=
  fun j => if i = j then 1 else 0

def marker {p : ℕ} : Set (W p) :=
  {w |
    w = basis 0 ∨ w = -basis 0 ∨
    w = basis 1 ∨ w = -basis 1 ∨
    w = basis 2 ∨ w = -basis 2 ∨
    w = basis 0 + basis 2 ∨ w = -(basis 0 + basis 2) ∨
    w = basis 0 + (2 : ZMod p) • basis 1 + (3 : ZMod p) • basis 2 ∨
    w = -(basis 0 + (2 : ZMod p) • basis 1 + (3 : ZMod p) • basis 2)}

def markerSection {p : ℕ} : Set (G p) :=
  {g | ∃ w, w ∈ marker ∧ g = (w, hZero)}

def planeSectionWithRoot {p : ℕ} (ω : ZMod p) (t : Fin 5) : Set (G p) :=
  {g | ∃ w, w ∈ plane t ∧ g = (w, hSlope ω t)}

def inverseSection {p : ℕ} (ω : ZMod p) (t : Fin 5) : Set (G p) :=
  gInv ω '' planeSectionWithRoot ω t

def sourceConnection {p : ℕ} (ω : ZMod p) : Set (G p) :=
  markerSection ∪ ⋃ t : Fin 5,
    (planeSectionWithRoot ω t ∪ inverseSection ω t)

def targetConnection {p : ℕ} (ω : ZMod p) : Set (G p) :=
  gauge '' sourceConnection ω

def leftCayleyEdge {p : ℕ} (ω : ZMod p) (S : Set (G p))
    (x y : G p) : Prop :=
  ∃ s, s ∈ S ∧ y = gMul ω s x

def kernelSet {p : ℕ} : Set (G p) :=
  {g | ∃ a : ZMod p, g.2 = (a, (0 : ZMod 3))}

def isGroupAutomorphism {p : ℕ} (ω : ZMod p) (φ : G p → G p) : Prop :=
  Function.Bijective φ ∧
    ∀ x y, φ (gMul ω x y) = gMul ω (φ x) (φ y)

def isLinearBijection {p : ℕ} (A : V p → V p) : Prop :=
  Function.Bijective A ∧
    (∀ x y, A (x + y) = A x + A y) ∧
    (∀ (a : ZMod p) x, A (a • x) = a • A x)

/-- Claim 37776: the normalized section translation is an explicit
left-Cayley graph isomorphism. -/
def claim_37776 : Prop :=
  ∀ p : ℕ, Nat.Prime p → p % 3 = 1 → ∀ ω : ZMod p,
    scalarCubeRoot ω →
      Function.Bijective (gauge (p := p)) ∧
        (∀ x y : G p,
          leftCayleyEdge ω (sourceConnection ω) x y ↔
            leftCayleyEdge ω (targetConnection ω) (gauge (g := x))
              (gauge (g := y)))

/-- Claim 37778: the normalized values on the five translated sections
are the quartic values. -/
def claim_37778 : Prop :=
  ∀ p : ℕ, Nat.Prime p → p % 3 = 1 → ∀ ω : ZMod p,
    scalarCubeRoot ω →
      ∀ t : Fin 5,
        (d ω)⁻¹ * dot3 (nSlope t) (tau (hSlope ω t)) =
          (3 : ZMod p) * (slopeValue t) ^ 4

/-- Claim 37780: the full rank-four kernel is characteristic and the
quotient orientation cannot be reversed. -/
def claim_37780 : Prop :=
  ∀ p : ℕ, Nat.Prime p → p % 3 = 1 → ∀ ω : ZMod p,
    scalarCubeRoot ω →
      (∀ φ : G p → G p, isGroupAutomorphism ω φ →
        φ '' kernelSet = kernelSet) ∧
      (¬ ∃ A : V p → V p,
        isLinearBijection A ∧
          ∀ v, A (ω • v) = (ω ^ 2) • A v) ∧
      (∀ φ : G p → G p, isGroupAutomorphism ω φ →
        ∀ x, (φ x).2.2 = x.2.2)

end

end MathlibPlus.Open.Research.R1542
