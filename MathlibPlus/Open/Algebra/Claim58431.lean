import Mathlib

universe u

namespace MathlibPlus.Open.Algebra

/--
The exact universal reading of admitted claim 58431.  In particular, `A^3 = 1`
is represented pointwise, without adding a fixed-point-free hypothesis that is
not present in the source claim.  The equation `3 • e = 2 • d + A d` records
the stated division-by-three formula via the inverse of the bijective tripling
map.
-/
def affineOrderThreeNormIdentity_claim58431 : Prop :=
  ∀ (L : Type*) [Fintype L] [AddCommGroup L] (A : L ≃+ L),
    (∀ x : L, A (A (A x)) = x) →
    Function.Bijective (fun x : L => 3 • x) →
    ∀ d : L, d + A d + A (A d) = 0 →
      ∃ e : L, e - A e = d ∧
        3 • e = 2 • d + A d ∧
        ∀ e' : L, e' - A e' = d → e' = e

end MathlibPlus.Open.Algebra

namespace MathlibPlus.Algebra.Claim58431

/-- The exact universal claim is refuted by the identity automorphism on a lifted
copy of `ZMod 2`.  The source's uniqueness assertion therefore needs an
additional hypothesis. --/
theorem not_affineOrderThreeNormIdentity_claim58431 :
    ¬ MathlibPlus.Open.Algebra.affineOrderThreeNormIdentity_claim58431.{u} := by
  intro h
  let L := ULift.{u} (ZMod 2)
  let A : L ≃+ L := AddEquiv.refl L
  have hA : ∀ x : L, A (A (A x)) = x := by
    intro x
    rfl
  have hthree_id (x : L) : 3 • x = x := by
    apply ULift.ext
    change 3 • x.down = x.down
    have h3 : (3 : ZMod 2) = 1 := by decide
    simp [nsmul_eq_mul, h3]
  have hthree : Function.Bijective (fun x : L => 3 • x) := by
    constructor
    · intro x y hxy
      simpa [hthree_id] using hxy
    · intro y
      exact ⟨y, hthree_id y⟩
  have hzero : (0 : L) + A 0 + A (A 0) = 0 := by
    simp [A]
  obtain ⟨e, he, hexplicit, huniq⟩ := h L A hA hthree 0 hzero
  have h0 : (0 : L) - A 0 = 0 := by simp [A]
  have h1 : ULift.up (1 : ZMod 2) - A (ULift.up (1 : ZMod 2)) = 0 := by
    simp [A]
  have h10 : ULift.up (1 : ZMod 2) = (0 : L) :=
    (huniq _ h1).trans (huniq 0 h0).symm
  have : (1 : ZMod 2) = 0 := by
    simpa using congrArg ULift.down h10
  norm_num at this

end MathlibPlus.Algebra.Claim58431
