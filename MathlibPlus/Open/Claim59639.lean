import Mathlib

namespace MathlibPlus.Open
namespace Claim59639

abbrev M3 := Matrix (Fin 3) (Fin 3) (ZMod 5)

def S : M3 := !![3, 1, 0; 3, 0, 1; 1, 0, 0]

def T : M3 := !![1, 1, 1; 2, 0, 4; 2, 0, 2]

def OddResidue (r : ℕ) : Prop := r ∈ ({1, 3, 5, 7} : Set ℕ)

def claim : Prop :=
  (∀ r : ℕ, OddResidue r → ∀ H : M3,
    H * S = T ^ r * H → Matrix.det H = 0) ∧
    ¬ ∃ r : ℕ, OddResidue r ∧ ∃ H : M3,
      Matrix.det H ≠ 0 ∧ H * S = T ^ r * H

end Claim59639
end MathlibPlus.Open
