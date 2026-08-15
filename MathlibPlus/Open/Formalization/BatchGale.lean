import Mathlib

namespace MathlibPlus.Open.FormalizationBatch

noncomputable section
open scoped BigOperators Matrix

/-- Claim 55599: the canonical F_5 Gale profile. -/
def claim_55599 : Prop := by
  classical
  let R := ZMod 5
  let I := Fin 5 ⊕ Fin 4
  let X : Matrix (Fin 5) (Fin 4) R :=
    !![2, 2, 0, 1;
       0, 4, 4, 2;
       2, 4, 4, 3;
       0, 2, 2, 1;
       4, 1, 0, 2]
  let D : Matrix (Fin 5) I R :=
    fun i j => Sum.elim (fun k => if i = k then 1 else 0) (fun k => X i k) j
  let U : Matrix (Fin 4) I R :=
    fun i j => Sum.elim (fun k => - X k i) (fun k => if i = k then 1 else 0) j
  let tensors : Set (Matrix (Fin 4) (Fin 5) R) :=
    {T | ∃ i : I, T = fun a b => U a i * D b i}
  exact
    U * D.transpose = 0 ∧
    Module.finrank R (Submodule.span R tensors) = 8 ∧
    (∀ c : I → R,
      (∀ a b, (∑ i, c i * U a i * D b i) = 0) ↔
        ∃ t : R, ∀ i, c i = t)

end
end MathlibPlus.Open.FormalizationBatch
