import Mathlib
import MathlibPlus.Open.Research.AdmittedBatch019ffedd

namespace MathlibPlus.Open.ResearchFormalization.R0410

open MathlibPlus.Open.Research.AdmittedBatch019ffedd

private def normalizedFactor {α : Type} [DecidableEq α]
    (F : Finset (Finset α)) : Prop :=
  F.Nonempty ∧
    (∅ : Finset α) ∉ F ∧
      unionClosed F ∧ emptyTotalIntersection F

/-- Claim 21079: normalized pair-fiber factors of size `N - 2` at least
 eleven cannot have a five-member union product. -/
def pairFiberApplication_claim21079 : Prop :=
  ∀ {α : Type} [DecidableEq α]
    (N k l : ℕ)
    (A : Fin k → Finset (Finset α))
    (B : Fin l → Finset (Finset α)),
    (∀ i : Fin k,
      normalizedFactor (A i) ∧
        (A i).card = N - 2 ∧
          11 ≤ (A i).card) →
      (∀ j : Fin l,
        normalizedFactor (B j) ∧
          (B j).card = N - 2 ∧
            11 ≤ (B j).card) →
        ∀ i : Fin k, ∀ j : Fin l,
          (unionProduct (A i) (B j)).card = 5 → False

end MathlibPlus.Open.ResearchFormalization.R0410
