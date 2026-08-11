import Mathlib

namespace MathlibPlus.Combinatorics

open scoped BigOperators

theorem claim23846_hypermatching_swap_factorization
    {R : Type*} [CommRing R] [DecidableEq R]
    (A B C D : Finset R)
    (hAC : Disjoint A C) (hBD : Disjoint B D)
    (hAD : Disjoint A D) (hBC : Disjoint B C) :
    let P : Finset R → Polynomial R :=
      fun S => (∏ a ∈ S, (Polynomial.X + Polynomial.C a))
    let SE := P (A ∪ C) + P (B ∪ D)
    let SF := P (A ∪ D) + P (B ∪ C)
    SE - SF = (P A - P B) * (P C - P D) := by
  classical
  simp only
  rw [Finset.prod_union hAC, Finset.prod_union hBD,
    Finset.prod_union hAD, Finset.prod_union hBC]
  ring

end MathlibPlus.Combinatorics
