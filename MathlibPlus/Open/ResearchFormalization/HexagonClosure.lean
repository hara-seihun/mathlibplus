import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

/--
The algebraic closure implication in the differentiated unit-hexagon block:
when the two auxiliary `w`-side rates agree, linear independence of the two
orthogonal track directions synchronizes both remaining opposite pairs.
-/
def differentiatedUnitHexagonClosureBlock : Prop :=
  ∀ (a a' b b' c c' : ℝ) (u v w : EuclideanSpace ℝ (Fin 2)),
    inner ℝ u v = 0 →
      LinearIndependent ℝ ![u, v] →
        (a - a') • u + (b - b') • v + (c - c') • w = 0 →
        c = c' → a = a' ∧ b = b'

end MathlibPlus.Open.ResearchFormalization
