import Mathlib

namespace MathlibPlus.Combinatorics.Claim56232

open scoped BigOperators

/-- Sum of the squares of pairwise sums, with each unordered pair of list
positions taken once in list order. -/
def pairSquareSum {R : Type*} [CommRing R] : List R → R
  | [] => 0
  | x :: xs => (xs.map (fun y => (x + y) ^ 2)).sum + pairSquareSum xs

lemma pairSquareSum_cross {R : Type*} [CommRing R] (x : R) (xs : List R) :
    (xs.map (fun y => (x + y) ^ 2)).sum =
      (xs.length : R) * x ^ 2 + 2 * x * xs.sum +
        (xs.map (fun y => y ^ 2)).sum := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      rw [ih]
      push_cast
      ring

/-- The pointwise quadratic identity used before pair localization. -/
theorem pairLocalization_quadraticIdentity {R : Type*} [CommRing R] (xs : List R) :
    xs.sum ^ 2 = pairSquareSum xs -
      ((xs.length : R) - 2) * (xs.map (fun x => x ^ 2)).sum := by
  induction xs with
  | nil => simp [pairSquareSum]
  | cons x xs ih =>
      simp only [List.sum_cons, List.map_cons, List.length_cons]
      rw [pairSquareSum, pairSquareSum_cross]
      rw [show (x + xs.sum) ^ 2 = x ^ 2 + 2 * x * xs.sum + xs.sum ^ 2 by ring]
      rw [ih]
      push_cast
      ring

end MathlibPlus.Combinatorics.Claim56232
