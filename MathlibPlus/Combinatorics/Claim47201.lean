import Mathlib

namespace MathlibPlus.Combinatorics

/--
The degree-count identity in admitted claim 47201.  For a family of selected
four-sets, the sum of the selected-set incidences over all vertices is four
 times the number of vertices.
-/
theorem sumSelectedSetDegrees_eq_four_mul_claim47201
    {n : ℕ} (B : Fin n → Finset (Fin n))
    (hcard : ∀ i, (B i).card = 4) :
    (∑ x : Fin n, ∑ i : Fin n, if x ∈ B i then 1 else 0) = 4 * n := by
  classical
  rw [Finset.sum_comm]
  have hcount : ∀ i : Fin n,
      (∑ x : Fin n, if x ∈ B i then 1 else 0) = (B i).card := by
    intro i
    simpa using (Finset.sum_boole (fun x : Fin n => x ∈ B i) (Finset.univ : Finset (Fin n)))
  simp_rw [hcount, hcard]
  simp
  omega

/--
The final arithmetic core of admitted claim 47201: the upper bound on the
number of degree-pairs and the Cauchy--Schwarz lower bound force an underlying
polygon size of at least eight.  The geometric construction, circle
intersection argument, and the derivation of these two bounds are intentionally
kept as explicit hypotheses because MathlibPlus has no polygon/circle carrier
for the source-specific argument.
-/
theorem convexPolygonCountingCore_claim47201
    (n : ℕ) (d : Fin n → ℕ) (hn : 1 ≤ n)
    (hupper : ∑ x, Nat.choose (d x) 2 ≤ n * (n - 2))
    (hlower : 6 * n ≤ ∑ x, Nat.choose (d x) 2) :
    8 ≤ n := by
  have hcombined : 6 * n ≤ n * (n - 2) := le_trans hlower hupper
  by_contra hnot
  have hnle : n ≤ 7 := by omega
  interval_cases n <;> norm_num at hn hcombined

end MathlibPlus.Combinatorics
