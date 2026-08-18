import MathlibPlus.Algebra.Claim29919
import MathlibPlus.Open.ResearchFormalization.R1061.Claim29924

namespace MathlibPlus.Open.ResearchFormalization.R1061Claim29925

noncomputable section

open MathlibPlus.Open.ResearchFormalization.R1061.Claim29924

/-- Claim 29925: an exponent pair in the exact multiplicity-one positive-root
    factorization packet can only be `(1,2)`. -/
def claim29925 : Prop :=
  ∀ {p q : ℕ} {δ : ℚ},
    0 < p →
      p < q →
        δ ≠ 0 →
          δ ≠ (p : ℚ) →
            δ ≠ (q : ℚ) →
              Nonempty (PositiveRootPacket p q δ) →
                (p, q) = (1, 2)

end

end MathlibPlus.Open.ResearchFormalization.R1061Claim29925
