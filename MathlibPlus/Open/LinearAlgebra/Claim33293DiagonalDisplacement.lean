import Mathlib

noncomputable section

namespace MathlibPlus.Open.LinearAlgebra.Claim33293DiagonalDisplacement

abbrev Plane (p : ℕ) := Fin 2 → ZMod p

def diagonalMultiplier (p : ℕ) (a d : ZMod p) :
    Matrix (Fin 2) (Fin 2) (ZMod p) :=
  Matrix.diagonal (fun i => if i = 0 then a else d)

noncomputable def displacementImage
    (p : ℕ) (a d : ZMod p) [Fact p.Prime] :
    Submodule (ZMod p) (Plane p) :=
  LinearMap.range
    (Matrix.toLin' (diagonalMultiplier p a d - (1 : Matrix (Fin 2) (Fin 2) (ZMod p))))

noncomputable def coordinateAxis
    (p : ℕ) (i : Fin 2) [Fact p.Prime] :
    Submodule (ZMod p) (Plane p) :=
  Submodule.span (ZMod p) {Pi.single i (1 : ZMod p)}

/-- Claim 33293: a nonidentity invertible diagonal multiplier has image one
coordinate axis or the whole plane; containment in a non-coordinate line
forces the multiplier to be the identity. -/
def claim33293_diagonalMultiplierDisplacement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], Odd p →
    ∀ (a d : ZMod p),
      IsUnit a → IsUnit d →
      (diagonalMultiplier p a d ≠
          (1 : Matrix (Fin 2) (Fin 2) (ZMod p)) →
        displacementImage p a d = coordinateAxis p 0 ∨
          displacementImage p a d = coordinateAxis p 1 ∨
          displacementImage p a d = ⊤) ∧
      ∀ V : Submodule (ZMod p) (Plane p),
        Module.finrank (ZMod p) V = 1 →
        V ≠ coordinateAxis p 0 →
        V ≠ coordinateAxis p 1 →
        displacementImage p a d ≤ V →
        diagonalMultiplier p a d =
          (1 : Matrix (Fin 2) (Fin 2) (ZMod p))

end MathlibPlus.Open.LinearAlgebra.Claim33293DiagonalDisplacement
