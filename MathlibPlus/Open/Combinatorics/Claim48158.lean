import Mathlib

open BigOperators
open scoped BigOperators

namespace MathlibPlus.Open.Combinatorics

/--
Faithful formal statement of claim 48158.  The graph is the finite spider with
one centre, `r` direct leaves, and two arms of length three.  Its independence
polynomial is defined as the independent-set generating polynomial, so the
assertion is about the actual graph rather than a detached polynomial formula.
-/
def centreDecomposition_claim48158 : Prop := by
  classical
  exact ∀ r : ℕ,
    let G : SimpleGraph (Fin (r + 7)) :=
      SimpleGraph.fromRel (fun v w =>
        (v.val = 0 ∧ 1 ≤ w.val ∧ w.val ≤ r) ∨
        (v.val = 0 ∧ w.val = r + 1) ∨
        (v.val = r + 1 ∧ w.val = r + 2) ∨
        (v.val = r + 2 ∧ w.val = r + 3) ∨
        (v.val = 0 ∧ w.val = r + 4) ∨
        (v.val = r + 4 ∧ w.val = r + 5) ∨
        (v.val = r + 5 ∧ w.val = r + 6))
    let I : Polynomial ℤ :=
      ∑ S : Finset (Fin (r + 7)),
        if G.IsIndepSet (S : Set (Fin (r + 7))) then
          Polynomial.X ^ S.card
        else 0
    I =
      (1 + Polynomial.X) ^ r *
          (1 + 3 * Polynomial.X + Polynomial.X ^ 2) ^ 2 +
        Polynomial.X * (1 + 2 * Polynomial.X) ^ 2

end MathlibPlus.Open.Combinatorics
