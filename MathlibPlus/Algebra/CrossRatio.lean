import Mathlib

/-!
# Centered cross-ratio algebra

The source's cross-ratio orientation is represented by its denominator-free
relation.  The three nonzero centered differences are retained as hypotheses;
the two displayed translations themselves are algebraic identities and do not
need those hypotheses for their kernel proof.
-/

namespace MathlibPlus.Algebra.CrossRatio

/-- The denominator-free cross-ratio relation used by claim 25470. -/
def equation (Ka Kb Kc Kd lam : ℝ) : Prop :=
  (Ka - Kd) * (Kb - Kc) = lam * (Ka - Kc) * (Kb - Kd)

/-- Centering at `Kc` translates the denominator-free cross-ratio equation to
`(A-D)B = lam*A*(B-D)`, with `A`, `B`, and `D` as in the source. -/
theorem translationCentered (Ka Kb Kc Kd lam : ℝ)
    (hA : Ka - Kc ≠ 0) (hB : Kb - Kc ≠ 0) (hD : Kd - Kc ≠ 0) :
    equation Ka Kb Kc Kd lam ↔
      let A := Ka - Kc
      let B := Kb - Kc
      let D := Kd - Kc
      (A - D) * B = lam * A * (B - D) := by
  dsimp [equation]
  constructor <;> intro h <;> linarith

/-- The centered cross-ratio relation factors as
`D*(lam*A-B) = (lam-1)*A*B`. -/
theorem translationFactorized (Ka Kb Kc Kd lam : ℝ)
    (hA : Ka - Kc ≠ 0) (hB : Kb - Kc ≠ 0) (hD : Kd - Kc ≠ 0) :
    (let A := Ka - Kc
     let B := Kb - Kc
     let D := Kd - Kc
     (A - D) * B = lam * A * (B - D)) ↔
      (let A := Ka - Kc
       let B := Kb - Kc
       let D := Kd - Kc
       D * (lam * A - B) = (lam - 1) * A * B) := by
  dsimp
  constructor <;> intro h <;> linarith

/-!
Formalization of admitted claim 3303.  The index inequality is retained even
though the algebraic identity itself is valid without using it.  `star` is
Mathlib's complex-conjugation operation, and the left side is norm squared.
-/

/-- The squared cross-ratio of the two displayed points has the real form in the claim. -/
theorem pairDistanceIdentity
    {ι : Type*} (y t : ι → ℝ) {j k : ι} (_hjk : j ≠ k) :
    let sⱼ : ℂ := (y j : ℂ) - Complex.I * (t j : ℂ)
    let sₖ : ℂ := (y k : ℂ) - Complex.I * (t k : ℂ)
    ‖(sⱼ - sₖ) / (sⱼ + star sₖ)‖ ^ 2 =
      ((t j - t k) ^ 2 + (y j - y k) ^ 2) /
        ((t j - t k) ^ 2 + (y j + y k) ^ 2) := by
  dsimp
  rw [Complex.sq_norm, Complex.normSq_div]
  simp [Complex.normSq_apply]
  ring

end MathlibPlus.Algebra.CrossRatio
