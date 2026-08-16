import Mathlib

namespace MathlibPlus.Open

def distinctPartialSumsForNearFullFiniteField : Prop :=
  ∀ (p : ℕ), Nat.Prime p →
    ∀ (A : Finset {x : Fin p // x.val ≠ 0}),
      ((Finset.univ : Finset {x : Fin p // x.val ≠ 0}) \ A).card ≤ 2 →
      ∃ order : Fin A.card ≃ {a // a ∈ A},
        ∀ ⦃i j : Fin A.card⦄, i ≠ j →
          Finset.sum (Finset.univ.filter (fun k : Fin A.card => k ≤ i))
              (fun k => ((order k).val.val.val : ZMod p)) ≠
            Finset.sum (Finset.univ.filter (fun k : Fin A.card => k ≤ j))
              (fun k => ((order k).val.val.val : ZMod p))

end MathlibPlus.Open
