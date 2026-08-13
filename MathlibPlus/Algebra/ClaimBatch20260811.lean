import Mathlib

namespace MathlibPlus.Algebra.ClaimBatch20260811

/-- Claim 21213: the two displayed finite census arithmetic receipts. -/
theorem genericSignatureArithmetic_claim21213 :
    2 ^ 6 * (3 ^ 3 - 2 ^ 3) = (1216 : ℕ) ∧
      2 ^ 6 * (6 ^ 3 - 5 ^ 3) = (5824 : ℕ) := by
  norm_num

/-- Claim 36298: the parent context has enough weight for every extracted
marker below the largest admissible marker.  The half-order condition is
written as `2*m < n`. -/
theorem legalParentWeight_claim36298
    (m n c j jstar : ℕ)
    (horder : c + m = n - 1)
    (hhalf : 2 * m < n)
    (hstar : jstar ≤ m - 1)
    (hj : j ≤ jstar) :
    j ≤ c := by
  omega

/-- Claim 6935: at most eight forbidden elements cannot cover the eighteen
listed rational-ray slots. -/
theorem finiteRationalRaySelection_claim6935
    (forbidden : Finset (Fin 18))
    (hforbidden : forbidden.card ≤ 8) :
    ∃ d : Fin 18, d ∉ forbidden := by
  by_contra h
  push Not at h
  have hsub : (Finset.univ : Finset (Fin 18)) ⊆ forbidden := by
    intro d hd
    exact h d
  have hcard := Finset.card_le_card hsub
  norm_num at hcard
  omega

end MathlibPlus.Algebra.ClaimBatch20260811
