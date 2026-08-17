import Mathlib

namespace MathlibPlus.Open.RepresentationTheory.R1381

abbrev Q8 := QuaternionGroup 2
abbrev Q8Vector (p : ℕ) := Fin 2 → ZMod p
abbrev Q8GL2 (p : ℕ) := Matrix.GeneralLinearGroup (Fin 2) (ZMod p)

def q8MatrixI (p : ℕ) : Matrix (Fin 2) (Fin 2) (ZMod p) :=
  !![0, 1; -1, 0]

def q8MatrixJ (p : ℕ) (a b : ZMod p) : Matrix (Fin 2) (Fin 2) (ZMod p) :=
  !![a, b; b, -a]

def q8MatrixMinusIdentity (p : ℕ) : Matrix (Fin 2) (Fin 2) (ZMod p) :=
  -(1 : Matrix (Fin 2) (Fin 2) (ZMod p))

def q8InvariantSubmodule {p : ℕ}
    (ρ : Q8 →* Q8GL2 p) (W : Submodule (ZMod p) (Q8Vector p)) : Prop :=
  ∀ g : Q8, ∀ v : Q8Vector p, v ∈ W →
    Matrix.mulVec (ρ g : Matrix (Fin 2) (Fin 2) (ZMod p)) v ∈ W

def q8TwoDimensionalIrreducible {p : ℕ}
    (ρ : Q8 →* Q8GL2 p) : Prop :=
  ∀ W : Submodule (ZMod p) (Q8Vector p),
    q8InvariantSubmodule ρ W → W = ⊥ ∨ W = ⊤

/-- The explicit odd-prime matrix construction: the displayed matrices are
quaternion generators, and the resulting representation is faithful and has
no nonzero proper invariant subspace. -/
def claim38421 : Prop :=
  ∀ (p : ℕ), Nat.Prime p → Odd p →
    ∃ a b : ZMod p,
      a ^ 2 + b ^ 2 = -1 ∧
      let i := q8MatrixI p
      let j := q8MatrixJ p a b
      let minus := q8MatrixMinusIdentity p
      i * i = minus ∧
        j * j = minus ∧
        i * j = -(j * i) ∧
        ∃ ρ : Q8 →* Q8GL2 p,
          (ρ (QuaternionGroup.a 1) : Matrix (Fin 2) (Fin 2) (ZMod p)) = i ∧
          (ρ (QuaternionGroup.xa 0) : Matrix (Fin 2) (Fin 2) (ZMod p)) = j ∧
          MonoidHom.ker ρ = ⊥ ∧
          (ρ (QuaternionGroup.a 2) : Matrix (Fin 2) (Fin 2) (ZMod p)) = minus ∧
          q8TwoDimensionalIrreducible ρ

end MathlibPlus.Open.RepresentationTheory.R1381
