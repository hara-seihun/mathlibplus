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

end MathlibPlus.Algebra.CrossRatio
