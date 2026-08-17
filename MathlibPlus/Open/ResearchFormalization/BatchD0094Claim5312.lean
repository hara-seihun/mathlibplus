import Mathlib
import MathlibPlus.Open.ResearchFormalization.AdmittedCharts
import MathlibPlus.Open.Edge13Modes

namespace MathlibPlus.Open.ResearchFormalization.D0094Claim5312

open MathlibPlus.Open.Edge13
open MathlibPlus.Open.ResearchFormalization.Batch

abbrev EdgePolynomial := MathlibPlus.Open.Edge13.Polynomial

noncomputable def edge13Evaluation
    (values : Variable → ℤ) (P : EdgePolynomial) : ℤ :=
  MvPolynomial.eval values P

def coordinateEvaluation
    (x a b m y n z c d : ℕ) : Variable → ℤ
  | .a => a
  | .b => b
  | .m => m
  | .n => n
  | .c => c
  | .d => d
  | .x => x
  | .y => y
  | .z => z

noncomputable def coordinateValue
    (x a b m y n z c d : ℕ) (P : EdgePolynomial) : ℤ :=
  edge13Evaluation (coordinateEvaluation x a b m y n z c d) P

/-- Claim 5312: on the positive ordered branch-four chart, the displayed
residual factors have the stated forced zero sets; the quadratic residual is
independent of pendant variables and, since the metric coordinates are
positive, its zero set is exactly the pure metric relation. -/
def claim5312 : Prop :=
  ∀ (x a b m y n z c d : ℕ),
    orderedBranchFourPathChart x a b m y n z c d →
      (x = y →
        coordinateValue x a b m y n z c d
          MathlibPlus.Open.Edge13.residualBend = 0) ∧
      (y = z →
        coordinateValue x a b m y n z c d
          MathlibPlus.Open.Edge13.residualBend = 0) ∧
      (m = n →
        coordinateValue x a b m y n z c d
          MathlibPlus.Open.Edge13.residualLeaf = 0) ∧
      ((x : ℤ) - y + z = 0 →
        coordinateValue x a b m y n z c d
          MathlibPlus.Open.Edge13.residualLeaf = 0) ∧
      (coordinateValue x a b m y n z c d
          MathlibPlus.Open.Edge13.residualQuad = 0 ↔
        (x : ℤ) ^ 2 - (x : ℤ) * z - (y : ℤ) ^ 2 + (z : ℤ) ^ 2 = 0) ∧
      (∀ φ ψ : Variable → ℤ,
        φ .x = ψ .x → φ .y = ψ .y → φ .z = ψ .z →
          edge13Evaluation φ MathlibPlus.Open.Edge13.residualQuad =
            edge13Evaluation ψ MathlibPlus.Open.Edge13.residualQuad)

end MathlibPlus.Open.ResearchFormalization.D0094Claim5312
