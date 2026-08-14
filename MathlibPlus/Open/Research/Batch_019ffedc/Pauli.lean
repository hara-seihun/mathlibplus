import Mathlib

namespace MathlibPlus.Open.Algebra

/-- The Pauli span filtration and its transverse two-plane. -/
def arthurPauliFiltration : Prop :=
  let I : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 1]
  let X : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
  let Z : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]
  let Y : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]
  ∃ F0 F1 R P : Submodule ℂ (Matrix (Fin 2) (Fin 2) ℂ),
    P = Submodule.span ℂ ({I, X, Z, Y} : Set (Matrix (Fin 2) (Fin 2) ℂ)) ∧
    P = ⊤ ∧
    F0 = Submodule.span ℂ ({I, X} : Set (Matrix (Fin 2) (Fin 2) ℂ)) ∧
    F1 = P ∧
    R = Submodule.span ℂ ({Z, Y} : Set (Matrix (Fin 2) (Fin 2) ℂ)) ∧
    F0 ⊓ R = ⊥ ∧ F0 ⊔ R = P

end MathlibPlus.Open.Algebra
