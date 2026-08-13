import Mathlib

namespace MathlibPlus.Combinatorics.Claim16849

private theorem sumSquaresFloorTransfer (N : List ℕ) :
    (N.map (fun n => n ^ 2 / 25)).sum ≤ N.sum ^ 2 / 25 := by
  induction N with
  | nil => simp
  | cons a N ih =>
      rw [List.map_cons, List.sum_cons]
      have hcross : a ^ 2 + N.sum ^ 2 ≤ (a + N.sum) ^ 2 := by
        nlinarith [Nat.zero_le (2 * a * N.sum)]
      calc
        a ^ 2 / 25 + (N.map (fun n => n ^ 2 / 25)).sum ≤
            a ^ 2 / 25 + N.sum ^ 2 / 25 := Nat.add_le_add_left ih _
        _ ≤ (a ^ 2 + N.sum ^ 2) / 25 := by omega
        _ ≤ (a + N.sum) ^ 2 / 25 := Nat.div_le_div_right hcross

private theorem componentwiseSumBound {N β : List ℕ}
    (hbound : List.Forall₂ (fun n b => b ≤ n ^ 2 / 25) N β) :
    β.sum ≤ (N.map (fun n => n ^ 2 / 25)).sum := by
  cases hbound with
  | nil => simp
  | cons hhead htail =>
      simp only [List.sum_cons, List.map_cons]
      exact Nat.add_le_add hhead (componentwiseSumBound htail)

/-- Componentwise bounds by the quadratic floor transfer to the total.  The
component values and total are explicit list carriers for the source's beta
invariants; the graph-component semantics remain outside this arithmetic core. -/
theorem componentwiseFloorTransfer_claim16849
    (N β : List ℕ) (βG : ℕ)
    (hdecomp : βG = β.sum)
    (hbound : List.Forall₂ (fun n b => b ≤ n ^ 2 / 25) N β) :
    βG ≤ N.sum ^ 2 / 25 := by
  rw [hdecomp]
  exact (componentwiseSumBound hbound).trans (sumSquaresFloorTransfer N)

end MathlibPlus.Combinatorics.Claim16849
