import Mathlib

namespace MathlibPlus.Algebra.Claim26915

/-- Claim 26915: evaluation at zero specializes a finite polynomial affine
relation, with the specialized terms defined by Qbar_i = Q_i(0). -/
def specialization_preserves_relation : Prop :=
  ∀ {K : Type*} [Semiring K] {n : ℕ}
    (c : Fin n → K) (Q : Fin n → Polynomial K),
    (∑ i : Fin n, c i • Q i = 0) →
      let Qbar : Fin n → K := fun i => (Q i).eval 0
      ∑ i : Fin n, c i * Qbar i = 0

end MathlibPlus.Algebra.Claim26915
