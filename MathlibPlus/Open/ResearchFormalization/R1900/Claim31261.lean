import MathlibPlus.Open.ResearchFormalization.R1900.Claim31268

namespace MathlibPlus.Open.ResearchFormalization.R1900.Claim31261

noncomputable section

open MathlibPlus.Open.ResearchFormalization.R1900.Claim31268

attribute [local instance] Classical.decEq Classical.propDecidable

private def uniformFamily {α : Type*} [DecidableEq α]
    (n : ℕ) (G : Finset (Finset α)) : Prop :=
  ∀ B ∈ G, B.card = n

private def exactTraceClass {α : Type*} [DecidableEq α]
    (A T : Finset α) (G : Finset (Finset α)) : Finset (Finset α) :=
  (G.erase A).filter (fun B => A ∩ B = T)

private def residualFamily {α : Type*} [DecidableEq α]
    (A T : Finset α) (G : Finset (Finset α)) : Finset (Finset α) :=
  (exactTraceClass A T G).image (fun B => B \ A)

private def liftResidualFamily {α : Type*} [DecidableEq α]
    (T : Finset α) (K : Finset (Finset α)) : Finset (Finset α) :=
  K.image (fun R => T ∪ R)

private def sunflowerWithCore {α : Type*} [DecidableEq α]
    (C : Finset α) (I : Finset (Finset α)) : Prop :=
  ∀ ⦃B⦄, B ∈ I → ∀ ⦃D⦄, D ∈ I → B ≠ D → B ∩ D = C

private def occupiedTrace {α : Type*} [DecidableEq α]
    (A T : Finset α) (G : Finset (Finset α)) : Prop :=
  ∃ B, B ∈ G.erase A ∧ A ∩ B = T

/-- Exact-trace residuals retain distinctness and uniformity, lift residual
sunflowers with core `C` to core `T ∪ C`, and turn a residual matching of
size `k-1` into a sunflower after adjoining the pivot. -/
def exactResidualFidelityAndMatching_claim31261 : Prop :=
  ∀ {α : Type*} [Fintype α] [DecidableEq α]
    (n k : ℕ) (G : Finset (Finset α)) (A T : Finset α),
    3 ≤ k →
      uniformFamily n G →
        kSunflowerFree k G →
          A ∈ G →
            occupiedTrace A T G →
              (∀ B ∈ exactTraceClass A T G,
                (B \ A).card = n - T.card) ∧
              (∀ B ∈ exactTraceClass A T G,
                ∀ D ∈ exactTraceClass A T G,
                  B \ A = D \ A → B = D) ∧
              (∀ B ∈ exactTraceClass A T G,
                T ∪ (B \ A) = B) ∧
              (∀ (C : Finset α) (K : Finset (Finset α)),
                K.card = k →
                  K ⊆ residualFamily A T G →
                    sunflowerWithCore C K →
                      (liftResidualFamily T K).card = k ∧
                      liftResidualFamily T K ⊆ G ∧
                      sunflowerWithCore (T ∪ C)
                        (liftResidualFamily T K)) ∧
              (∀ (K : Finset (Finset α)),
                K.card = k - 1 →
                  K ⊆ residualFamily A T G →
                    (∀ ⦃R⦄, R ∈ K →
                      ∀ ⦃S⦄, S ∈ K → R ≠ S → Disjoint R S) →
                      (insert A (liftResidualFamily T K)).card = k ∧
                      insert A (liftResidualFamily T K) ⊆ G ∧
                      sunflowerWithCore T
                        (insert A (liftResidualFamily T K))) ∧
              kSunflowerFree k (residualFamily A T G) ∧
              matchingAtMost k (residualFamily A T G)

end

end MathlibPlus.Open.ResearchFormalization.R1900.Claim31261
