import Mathlib

namespace MathlibPlus.Algebra.Claim52681

/-- The zero-relative-derivative subspace statement in claim 52681.
Finiteness is not needed for this algebraic lemma, so the formal statement
retains the stronger arbitrary `ZMod 3`-module scope. -/
theorem zeroRelativeDerivativeSubspace
    {A : Type*} [AddCommGroup A] [Module (ZMod 3) A]
    (p : A → ZMod 3) (hp0 : p 0 = 0)
    (hpodd : ∀ a : A, p (-a) = -p a) :
    let Zp : Set A :=
      {a | ∀ x : A, p (x + a) - p x - p a = 0}
    ∃ V : Submodule (ZMod 3) A, V.carrier = Zp ∧
      ∃ pV : V →ₗ[ZMod 3] ZMod 3, ∀ a : V, pV a = p a := by
  dsimp
  have hzero : ∀ x : A, p (x + 0) - p x - p 0 = 0 := by
    intro x
    simp [hp0]
  have hneg : ∀ (a : A),
      (∀ x : A, p (x + a) - p x - p a = 0) →
        ∀ x : A, p (x + (-a)) - p x - p (-a) = 0 := by
    intro a ha x
    have h : p x - p (x - a) - p a = 0 := by
      simpa only [sub_add_cancel] using ha (x - a)
    calc
      p (x + (-a)) - p x - p (-a) =
          p (x - a) - p x + p a := by
            rw [hpodd]
            abel
      _ = 0 := by linear_combination -h
  have hadd : ∀ (a b : A),
      (∀ x : A, p (x + a) - p x - p a = 0) →
      (∀ x : A, p (x + b) - p x - p b = 0) →
        ∀ x : A, p (x + (a + b)) - p x - p (a + b) = 0 := by
    intro a b ha hb x
    have h1 : p (x + (a + b)) - p (x + b) - p a = 0 := by
      convert ha (x + b) using 1; abel
    have h2 := hb x
    have h3 : p (a + b) - p b - p a = 0 := by
      convert ha b using 1; abel
    linear_combination h1 + h2 - h3
  let Zadd : AddSubgroup A :=
    { carrier := {a | ∀ x : A, p (x + a) - p x - p a = 0}
      zero_mem' := hzero
      add_mem' := by
        intro a b ha hb
        exact hadd a b ha hb
      neg_mem' := by
        intro a ha
        exact hneg a ha }
  let V : Submodule (ZMod 3) A := AddSubgroup.toZModSubmodule 3 Zadd
  have hpadd : ∀ (a b : V), p (a + b) = p a + p b := by
    intro a b
    have h : p ((a : A) + (b : A)) - p (b : A) - p (a : A) = 0 := by
      simpa [add_comm] using (a.property (b : A))
    linear_combination h
  let pAdd : V →+ ZMod 3 :=
    { toFun := fun a => p a
      map_zero' := hp0
      map_add' := by
        intro a b
        exact hpadd a b }
  let pV : V →ₗ[ZMod 3] ZMod 3 := pAdd.toZModLinearMap 3
  refine ⟨V, ?_, pV, ?_⟩
  · rfl
  · intro a
    rfl

end MathlibPlus.Algebra.Claim52681
