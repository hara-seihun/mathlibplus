import Mathlib

namespace MathlibPlus.LinearAlgebra

/--
Claim 24182: a nonzero square integer minor modulo a prime has nonzero
integer and rational determinants and certifies full rational column rank.
The row selector exposes the minor inside a possibly rectangular ambient
matrix; full column rank is expressed by triviality of the rational kernel.
-/
theorem claim24182_integerMinorModPrimeFullColumnRank
    {m n p : ℕ} (_hp : Nat.Prime p)
    (A : Matrix (Fin m) (Fin n) ℤ)
    (rows : Fin n → Fin m) (_hrows : Function.Injective rows)
    (hmod : ((Matrix.det (fun i j => A (rows i) j) : ℤ) : ZMod p) ≠ 0) :
    Matrix.det (fun i j => A (rows i) j) ≠ 0 ∧
      Matrix.det (fun i j => (A (rows i) j : ℚ)) ≠ 0 ∧
        ∀ x : Fin n → ℚ,
          (Matrix.mulVec (fun i j => (A i j : ℚ)) x = 0) → x = 0 := by
  let Bz : Matrix (Fin n) (Fin n) ℤ := fun i j => A (rows i) j
  let Bq : Matrix (Fin n) (Fin n) ℚ := Bz.map (fun z => (z : ℚ))
  have hmod' : (Bz.det : ZMod p) ≠ 0 := by
    simpa [Bz] using hmod
  have hdetZ : Bz.det ≠ 0 := by
    intro hzero
    apply hmod'
    rw [hzero]
    simp
  have hBq : Bq = (fun i j => (A (rows i) j : ℚ)) := by
    funext i j
    rfl
  have hdetQ : Bq.det ≠ 0 := by
    intro hzero
    have hcast := RingHom.map_det (Int.castRingHom ℚ) Bz
    have hcast' : (Bz.det : ℚ) = Bq.det := by
      simpa [Bq, Matrix.map_apply] using hcast
    apply hdetZ
    exact_mod_cast (hcast'.trans hzero)
  refine ⟨?_, ?_, ?_⟩
  · simpa [Bz]
  · rw [← hBq]
    exact hdetQ
  · intro x hx
    have hBx : Bq.mulVec x = 0 := by
      funext i
      have hi := congrFun hx (rows i)
      change (∑ j, (A (rows i) j : ℚ) * x j) = 0
      exact hi
    exact Matrix.eq_zero_of_mulVec_eq_zero hdetQ hBx

end MathlibPlus.LinearAlgebra
