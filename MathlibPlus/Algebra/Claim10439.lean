import Mathlib.Algebra.Group.Basic

namespace MathlibPlus.Algebra.Claim10439

/-- An additively idempotent element pairs trivially under any biadditive
pairing.  Additive cancellation is all that the displayed characteristic-zero
argument needs. -/
theorem idempotent_pairing_vanishes_claim10439
    {A X C : Type*} [AddSemigroup A] [AddSemigroup X] [AddCommGroup C]
    (B : A → X → C)
    (hleft : ∀ a a' x, B (a + a') x = B a x + B a' x)
    (hright : ∀ a x x', B a (x + x') = B a x + B a x')
    (e : A) (he : e + e = e) :
    ∀ x, B e x = 0 := by
  intro x
  have h := hleft e e x
  rw [he] at h
  have h' : 0 + B e x = B e x + B e x := by
    simpa using h
  exact (add_right_cancel h').symm

end MathlibPlus.Algebra.Claim10439
