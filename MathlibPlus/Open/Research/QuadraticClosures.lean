import Mathlib

namespace MathlibPlus.Open.Research.QuadraticClosures

abbrev QuadraticH := ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3
abbrev QuadraticE := ZMod 3 × QuadraticH

def quadraticG (h : QuadraticH) : QuadraticH :=
  let i := h.1
  let j := h.2.1
  let a := h.2.2.1
  let b := h.2.2.2.1
  let c := h.2.2.2.2
  (i, j, a + i * (i - 1), b + (2 * i - 1) * j, c + j ^ 2)

def quadraticPhi (α β γ δ ε i j : ZMod 3) : ZMod 3 :=
  α * i + β * j + γ * i ^ 2 + δ * i * j + ε * j ^ 2

def quadraticQ (α β γ δ ε : ZMod 3) (x : QuadraticE) : QuadraticE :=
  let z := x.1
  let h := x.2
  (z + quadraticPhi α β γ δ ε h.1 h.2.1, quadraticG h)

/-- The displayed quadratic quotient map is a permutation for every choice of coefficients. -/
def claim27830 : Prop :=
  ∀ α β γ δ ε : ZMod 3, Function.Bijective (quadraticQ α β γ δ ε)

def quadraticTranslation (v : QuadraticE) : Equiv.Perm QuadraticE :=
  Equiv.addRight v

def quadraticTranslationSet : Set (Equiv.Perm QuadraticE) :=
  Set.range quadraticTranslation

def quadraticGenerated (q : Equiv.Perm QuadraticE) : Subgroup (Equiv.Perm QuadraticE) :=
  Subgroup.closure
    (quadraticTranslationSet ∪
      (fun t => q⁻¹ * t * q) '' quadraticTranslationSet)

def quadraticTwoClosure (K : Set (Equiv.Perm QuadraticE)) : Set (Equiv.Perm QuadraticE) :=
  {q | ∀ x y, ∃ k, k ∈ K ∧ q x = k x ∧ q y = k y}

/-- The translation group and its displayed conjugate generate a group of order 3⁸. -/
def claim27833 : Prop :=
  ∀ α β γ δ ε : ZMod 3,
    ∃ q : Equiv.Perm QuadraticE,
      (∀ x, q x = quadraticQ α β γ δ ε x) ∧
      Nat.card (quadraticGenerated q) = 3 ^ 8

/-- The two regular translation subgroups are conjugate within the exact 2-closure. -/
def claim27836 : Prop :=
  ∀ α β γ δ ε : ZMod 3,
    ∃ q : Equiv.Perm QuadraticE,
      (∀ x, q x = quadraticQ α β γ δ ε x) ∧
      ∃ c : Equiv.Perm QuadraticE,
        c ∈ quadraticTwoClosure (quadraticGenerated q : Set (Equiv.Perm QuadraticE)) ∧
        Set.image (fun t => c⁻¹ * t * c) quadraticTranslationSet =
          Set.image (fun t => q⁻¹ * t * q) quadraticTranslationSet

end MathlibPlus.Open.Research.QuadraticClosures
