import MathlibPlus.Open.ResearchFormalization.R2654RawResultantRepair

namespace MathlibPlus.Open.ResearchFormalization.R2654

open MathlibPlus.Open.ResearchFormalization

/-- Claim 42181: the Boyd identity and the two denominator-cleared auxiliary
polynomial definitions, with the reciprocal polynomial convention fixed by the
reviewed Type-IV carrier. -/
def claim42181
    (n : ℕ) (A Astar R P1 P2 : Polynomial ℤ) : Prop :=
  A.Monic ∧
    A.natDegree = 2 * n + 1 ∧
      Astar = A.reverse ∧
        (∀ z : ℂ, z ≠ 0 →
          (z ^ 2 + 1) * evalIntComplex R z =
            z * evalIntComplex A z + evalIntComplex Astar z) ∧
          (∀ z : ℂ, z ≠ 0 →
            (z - 1) * evalIntComplex P1 z =
              z * evalIntComplex A z - evalIntComplex Astar z) ∧
            (∀ z : ℂ, z ≠ 0 →
              (z - 1) * evalIntComplex P2 z =
                z ^ 2 * evalIntComplex A z - evalIntComplex Astar z)

end MathlibPlus.Open.ResearchFormalization.R2654
