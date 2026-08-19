import Mathlib

namespace MathlibPlus.Open.Combinatorics

/-- Claim 1736: a strictly increasing row, its one-indexed Catalan
inequalities, and the associated finite set `B_K`. -/
def catalanAdmissibleRowSet_claim1736
    (d : ℕ) (K : Fin d → ℕ) (B : Finset ℕ) : Prop :=
  StrictMono K ∧
    (∀ i : Fin d, K i ≤ 2 * i.1 + 1) ∧
      B = insert 0 (Finset.univ.image (fun i : Fin d => K i + 1))

end MathlibPlus.Open.Combinatorics
