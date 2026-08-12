import MathlibPlus.Basic

namespace MathlibPlus.Algebra.Claim27457

/-!
The source's factor-triangle context gives the three differences from `H_c` and
uses `e = d + (λ - 1) * a`.  The displayed complementary differences are then
formal ring consequences.  The coprimality and nonzero assumptions from the
surrounding source are irrelevant to these identities and are not silently
used here.
-/

/-- The three complementary forest differences in claim 27457. -/
theorem complementaryDifferences_claim27457
    {R : Type*} [CommRing R]
    (k a d e lam H_a H_b H_c H_d : R)
    (h_ac : H_a - H_c = k * a * e)
    (h_dc : H_d - H_c = k * d * e)
    (h_bc : H_b - H_c = lam * k * a * d)
    (h_e : e = d + (lam - 1) * a) :
    H_a - H_d = -k * e * (d - a) ∧
      H_b - H_d = -k * d * (d - a) ∧
      H_a - H_b = -(lam - 1) * k * a * (d - a) := by
  refine ⟨?_, ?_, ?_⟩
  · calc
      H_a - H_d = (H_a - H_c) - (H_d - H_c) := by ring
      _ = k * a * e - k * d * e := by rw [h_ac, h_dc]
      _ = -k * e * (d - a) := by ring
  · calc
      H_b - H_d = (H_b - H_c) - (H_d - H_c) := by ring
      _ = lam * k * a * d - k * d * e := by rw [h_bc, h_dc]
      _ = -k * d * (d - a) := by rw [h_e]; ring
  · calc
      H_a - H_b = (H_a - H_c) - (H_b - H_c) := by ring
      _ = k * a * e - lam * k * a * d := by rw [h_ac, h_bc]
      _ = -(lam - 1) * k * a * (d - a) := by rw [h_e]; ring

end MathlibPlus.Algebra.Claim27457
