import MathlibPlus.LinearAlgebra.Claim7878Definitions

namespace MathlibPlus.Open.ResearchFormalization.C0048Claim7878

/-- Proof-free registry assertion for the standard tensor-basis involution and
its fourth-power relation. -/
def claim7878_dihedral_relations : Prop :=
  ∀ k : ℕ,
    (MathlibPlus.LinearAlgebra.claim7878S k) ∘
        MathlibPlus.LinearAlgebra.claim7878S k = id ∧
      (MathlibPlus.LinearAlgebra.claim7878R k) ∘
          MathlibPlus.LinearAlgebra.claim7878R k = id ∧
        (MathlibPlus.LinearAlgebra.claim7878SR k) ^[4] = id

/-- Proof-free registry assertion for exact order four when `k>0`. -/
def claim7878_SR_exact_order_four : Prop :=
  ∀ k : ℕ, 0 < k →
    (MathlibPlus.LinearAlgebra.claim7878SR k) ^[4] = id ∧
      (MathlibPlus.LinearAlgebra.claim7878SR k) ^[2] ≠ id

end MathlibPlus.Open.ResearchFormalization.C0048Claim7878
