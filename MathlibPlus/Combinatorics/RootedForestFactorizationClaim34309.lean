import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.List.Flatten

namespace MathlibPlus.Combinatorics

/-- The rooted-forest product factorization from claim 34309.  A root is
represented by the list of its child occurrences; `u` and `r` are the
unrooted and rooted factors, so the genuine factor is their sum. -/
theorem rootedForestProductFactorization_claim34309
    {R α : Type*} [CommSemiring R]
    (z : R) (roots : List (List α)) (u r : α → R) :
    (roots.map (fun branches => z * (branches.map (fun d => u d + r d)).prod)).prod =
      z ^ roots.length *
        (roots.flatten.map (fun d => u d + r d)).prod := by
  induction roots with
  | nil => simp
  | cons branches roots ih =>
      simp only [List.map_cons, List.prod_cons, List.length_cons,
        List.flatten_cons]
      rw [ih]
      simp [mul_assoc, mul_left_comm, mul_comm, pow_succ]

end MathlibPlus.Combinatorics
