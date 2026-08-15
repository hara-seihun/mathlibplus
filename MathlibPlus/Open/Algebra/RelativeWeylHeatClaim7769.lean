import Mathlib

namespace MathlibPlus.Open.Algebra.RelativeWeylHeat

/--
The balanced inverse and the dyadic optimality assertion from admitted Claim 7769.
The two-dimensional carrier is the quotient/trivial-sign basis supplied by the
same-locator repair context; `w` is its flip and `opNorm` is the induced norm.
-/
def claim7769 : Prop :=
  let V := Fin 2 → ℝ
  let w : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]
  let P : ℝ → Matrix (Fin 2) (Fin 2) ℝ := fun a =>
    ((1 + a) / 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
      ((1 - a) / 2) • w
  let matrixInverse :
      Matrix (Fin 2) (Fin 2) ℝ → Matrix (Fin 2) (Fin 2) ℝ → Prop :=
    fun A B => A * B = 1 ∧ B * A = 1
  let opNorm : Matrix (Fin 2) (Fin 2) ℝ → ℝ := fun A =>
    sSup {r : ℝ | ∃ x : V, ‖x‖ ≤ 1 ∧ r = ‖Matrix.mulVec A x‖}
  let Q : Matrix (Fin 2) (Fin 2) ℝ :=
    (3 / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) - (1 / 2 : ℝ) • w
  let sign : V := ![1, -1]
  let dyadicNorm : ℕ → ℝ := fun q =>
    Real.rpow 2 ((q : ℝ) / 2)
  let dyadicParameter : ℕ → ℝ := fun q =>
    Real.rpow 2 (-((q : ℝ) / 2))
  let universallySafe : ℕ → Prop := fun q =>
    Real.rpow 2 (-(q : ℝ)) ≤ (1 / 3 : ℝ)
  matrixInverse (P (1 / 2 : ℝ)) Q ∧
    (∀ B, matrixInverse (P (1 / 2 : ℝ)) B → B = Q) ∧
    Matrix.mulVec Q sign = (2 : ℝ) • sign ∧
    opNorm Q = 2 ∧
    (∀ q : ℕ,
      (∃ B, matrixInverse (P (dyadicParameter q)) B) ∧
        (∀ B, matrixInverse (P (dyadicParameter q)) B →
          opNorm B = dyadicNorm q)) ∧
    universallySafe 2 ∧
    (∀ q : ℕ, universallySafe q →
      dyadicNorm 2 ≤ dyadicNorm q ∧
        (dyadicNorm q = dyadicNorm 2 → q = 2))

end MathlibPlus.Open.Algebra.RelativeWeylHeat
