import Mathlib.Tactic

namespace MathlibPlus.Algebra.Claim19366

/--
Claim 19366: the two-atom diagonal second moment omits the independent-pair
cross term.  The outer products are written pointwise so that the statement
keeps the source's two-atom algebra without introducing a new public
construction.
-/
theorem diagonalSecondMoment_twoAtom_expansion
    {R : Type*} [CommRing R] (w₁ w₂ : R) (u v : Fin 2 → R) (i j : Fin 2) :
    let m : Fin 2 → R := fun k => w₁ * u k + w₂ * v k
    m i * m j =
      w₁ ^ 2 * (u i * u j) + w₂ ^ 2 * (v i * v j) +
        w₁ * w₂ * (u i * v j + v i * u j) := by
  dsimp
  ring

/--
An explicit nonzero, non-collinear two-atom instance has a diagonal state
whose off-diagonal entry is zero, while the full outer product has entry one.
This supplies the source claim's ``suitable'' witness without adding
hypotheses to the general expansion.
-/
theorem diagonalSecondMoment_twoAtom_witness :
    let u : Fin 2 → ℚ := fun i => if i = 0 then 1 else 0
    let v : Fin 2 → ℚ := fun i => if i = 1 then 1 else 0
    let w₁ : ℚ := 1
    let w₂ : ℚ := 1
    let m : Fin 2 → ℚ := fun k => w₁ * u k + w₂ * v k
    let X : Fin 2 → Fin 2 → ℚ :=
      fun i j => w₁ * u i * u j + w₂ * v i * v j
    u ≠ 0 ∧ v ≠ 0 ∧ (∀ a : ℚ, a • u ≠ v) ∧
      X ≠ fun i j => m i * m j := by
  dsimp
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    have h0 := congrFun h 0
    norm_num at h0
  · intro h
    have h1 := congrFun h 1
    norm_num at h1
  · intro a h
    have h1 := congrFun h 1
    norm_num at h1
  · intro h
    have h01 := congrFun (congrFun h 0) 1
    norm_num at h01

end MathlibPlus.Algebra.Claim19366
