import MathlibPlus.Open.Analysis.Claim3381

namespace MathlibPlus.Open.Analysis.Claim3384

/-- Claim 3384: the consecutive mixed-shift Casoratians satisfy exact
Desnanot--Jacobi condensation. -/
def desnanotJacobiCondensation : Prop :=
  ∀ m n : ℕ, 1 ≤ m →
    MathlibPlus.Open.Analysis.Claim3381.D (m + 1) n *
        MathlibPlus.Open.Analysis.Claim3381.D (m - 1) n =
      MathlibPlus.Open.Analysis.Claim3381.D m n ^ 2 -
        MathlibPlus.Open.Analysis.Claim3381.D m (n - 1) *
          MathlibPlus.Open.Analysis.Claim3381.D m (n + 1)

end MathlibPlus.Open.Analysis.Claim3384
