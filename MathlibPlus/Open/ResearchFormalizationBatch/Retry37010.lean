import Mathlib
import MathlibPlus.Open.ResearchFormalizationBatch_01a003cb_d995_7564_b82d_d782ff7e0528

namespace MathlibPlus.Open.ResearchFormalizationBatch.Retry37010

private def sortedDegreeProfile
    {α : Type*} [DecidableEq α]
    (𝓕 : Finset (Finset α)) (S r : ℕ) (A : Finset α) : Prop :=
  ∃ δ : Fin r → ℕ,
    (∀ i j : Fin r, i.val < j.val → δ i ≤ δ j) ∧
    (∀ q : ℕ,
      (A.filter (fun x =>
        MathlibPlus.Open.ResearchFormalizationBatch.coordinateDegree 𝓕 x = q)).card =
        (Finset.univ.filter (fun i : Fin r => δ i = q)).card) ∧
    (∀ i : Fin r, δ i > S ^ (i.val + 1))

/-- Exact complementary order-statistic profile for a member outside the
profile-good subtheorem. -/
def claim37010 : Prop :=
  ∀ (α : Type*) [DecidableEq α]
    (k S r : ℕ) (𝓕 : Finset (Finset α)),
    MathlibPlus.Open.ResearchFormalizationBatch.degreeFiltrationProfileContext
      k S r 𝓕 →
    (∀ A ∈ 𝓕,
      ¬ MathlibPlus.Open.ResearchFormalizationBatch.profileGoodMember
          𝓕 S r A ↔
        sortedDegreeProfile 𝓕 S r A) ∧
    (¬ MathlibPlus.Open.ResearchFormalizationBatch.profileGoodFamily
        𝓕 S r →
      ∃ A ∈ 𝓕,
        ¬ MathlibPlus.Open.ResearchFormalizationBatch.profileGoodMember
          𝓕 S r A ∧
        sortedDegreeProfile 𝓕 S r A)

end MathlibPlus.Open.ResearchFormalizationBatch.Retry37010
