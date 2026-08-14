import Mathlib

namespace MathlibPlus.Open.Hall

open scoped BigOperators

/-- The doubled Hall relation Frobenius matrix from Claim 11008. -/
def relationFrobenius : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(-3 : ℝ), 1; 0, -3]

/-- The literal Frobenius matrix from Claim 11008. -/
def literalFrobenius : Matrix (Fin 2) (Fin 2) ℝ :=
  (-3 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)

/-- Positive definiteness of a real matrix as a bilinear form on this coordinate space. -/
def positiveBilinearForm (P : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  ∀ v : Fin 2 → ℝ, v ≠ 0 →
    dotProduct v (P.mulVec v) > 0

/--
The explicit relation-jet calculation and the contrasting semisimple calculation
in Claim 11008.
-/
def relationJetInvariantFormsAreDegenerate : Prop :=
  (∀ P : Matrix (Fin 2) (Fin 2) ℝ,
      relationFrobenius.transpose * P * relationFrobenius =
        (9 : ℝ) • P →
      ∃ w : ℝ,
        P = !![(0 : ℝ), 0; 0, w] ∧ Matrix.det P = 0) ∧
    (∃ P : Matrix (Fin 2) (Fin 2) ℝ,
      positiveBilinearForm P ∧
      literalFrobenius.transpose * P * literalFrobenius = (9 : ℝ) • P)

end MathlibPlus.Open.Hall
