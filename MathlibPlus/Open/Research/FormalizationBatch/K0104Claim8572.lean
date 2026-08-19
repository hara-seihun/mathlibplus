import MathlibPlus.Open.Research.FormalizationBatch.K0104Claim8581

namespace MathlibPlus.Open.Research.FormalizationBatch.K0104Claim8572

open scoped BigOperators Interval
open MathlibPlus.Combinatorics.Claim8569
open MathlibPlus.Open.Research.FormalizationBatch.K0104Claim8581

noncomputable section

/-- The positive normalized m-hole ensemble on the exact reviewed carrier. -/
def positiveMHoleEnsemble_claim8572 : Prop :=
  ∀ (n m : ℕ) (x w : Fin n → ℝ),
    m ≤ n →
      StrictMono x →
        (∀ i : Fin n, 0 < x i) →
          (∀ i : Fin n, 0 < w i) →
            (∀ H : Finset (Fin n), H ∈ holeSets8581 n m →
              holeProbability8581 (m := m) x
                  (fun i => dualHoleWeight8581 x w i) H =
                holeMass8581 x (fun i => dualHoleWeight8581 x w i) H /
                  partitionFunction n m x
                    (fun i => dualHoleWeight8581 x w i)) ∧
              (∀ H : Finset (Fin n), H ∈ holeSets8581 n m →
                0 < holeProbability8581 (m := m) x
                  (fun i => dualHoleWeight8581 x w i) H) ∧
              (holeSets8581 n m).sum (fun H =>
                holeProbability8581 (m := m) x
                  (fun i => dualHoleWeight8581 x w i) H) = 1

end

end MathlibPlus.Open.Research.FormalizationBatch.K0104Claim8572
