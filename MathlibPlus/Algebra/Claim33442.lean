import Mathlib

namespace MathlibPlus.Algebra.Claim33442

/--
For a skew-product chart over `H`, conjugating a translation in the `H`
coordinate produces the displayed vertical displacement.  This is the exact
algebraic formula in admitted claim 33442, with `qinv` written explicitly;
the translation-equivariance hypothesis on `φ` makes it the inverse of `q`.
-/
theorem conjugatedTranslationDifferenceFormulas_claim33442
    {H : Type*} [AddCommGroup H]
    (t : H → ZMod 3) (φ : H → H)
    (hφ : ∀ h v : H, φ (h + v) = φ h + v)
    (z : ZMod 3) (h v : H) :
    let c : H := φ 0
    let φinv : H → H := fun w => w - c
    let q : ZMod 3 × H → ZMod 3 × H :=
      fun p => (p.1 + t p.2, φ p.2)
    let qinv : ZMod 3 × H → ZMod 3 × H :=
      fun p => (p.1 - t (φinv p.2), φinv p.2)
    let S : ZMod 3 × H → ZMod 3 × H :=
      fun p => (p.1, p.2 + v)
    let Sinv : ZMod 3 × H → ZMod 3 × H :=
      fun p => (p.1, p.2 - v)
    let T : ZMod 3 × H → ZMod 3 × H := fun p => qinv (S (q p))
    let δ : H → ZMod 3 := fun w => t w - t (w + v)
    (Sinv (T (z, h)) = (z + δ h, h)) ∧
      (T (Sinv (z, h)) = (z + δ (h - v), h)) := by
  dsimp
  have hφh : φ h = φ 0 + h := by
    simpa using hφ 0 h
  have hφhsub : φ (h - v) = φ 0 + (h - v) := by
    simpa using hφ 0 (h - v)
  rw [hφh, hφhsub]
  simp [sub_eq_add_neg, add_assoc, add_comm, add_left_comm]

end MathlibPlus.Algebra.Claim33442
