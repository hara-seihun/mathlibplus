import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

namespace MathlibPlus.LinearAlgebra

/-!
# Swap/reversal basis maps (claim 7878)

These are the explicit standard-tensor-basis carriers for `S` and `R = J_k ⊗ I`.
-/

/-- Reversal of the standard basis labels `0,...,k`. -/
def claim7878Rev (k : ℕ) (i : Fin (k + 1)) : Fin (k + 1) :=
  ⟨k - i.1, by omega⟩

/-- The swap `S` on the standard tensor basis. -/
def claim7878S (k : ℕ) :
    (Fin (k + 1) × Fin (k + 1)) → (Fin (k + 1) × Fin (k + 1)) :=
  fun p => (p.2, p.1)

/-- The basis permutation `R = J_k ⊗ I`. -/
def claim7878R (k : ℕ) :
    (Fin (k + 1) × Fin (k + 1)) → (Fin (k + 1) × Fin (k + 1)) :=
  fun p => (claim7878Rev k p.1, p.2)

def claim7878SR (k : ℕ) := claim7878S k ∘ claim7878R k

end MathlibPlus.LinearAlgebra
