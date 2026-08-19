import Mathlib

namespace MathlibPlus.Algebra.Claim12196Formalization

/-- The additive-idempotent part of Claim 12196. -/
theorem grothendieckAddGroup_idempotent_claim12196
    {M : Type*} [AddCommMonoid M] (e : M) (he : e + e = e) :
    Algebra.GrothendieckAddGroup.of e = 0 := by
  have h : Algebra.GrothendieckAddGroup.of e +
      Algebra.GrothendieckAddGroup.of e = Algebra.GrothendieckAddGroup.of e := by
    rw [← map_add, he]
  apply add_left_cancel (a := Algebra.GrothendieckAddGroup.of e)
  simpa using h

/-- The `Theta`-family consequence of Claim 12196, with its source-defined
idempotence exposed as the hypothesis on the family. -/
theorem grothendieckAddGroup_family_claim12196
    {S M : Type*} [AddCommMonoid M] (theta : S → M)
    (hTheta : ∀ s, theta s + theta s = theta s) :
    ∀ s, Algebra.GrothendieckAddGroup.of (theta s) = 0 := by
  intro s
  exact grothendieckAddGroup_idempotent_claim12196 (theta s) (hTheta s)

end MathlibPlus.Algebra.Claim12196Formalization
