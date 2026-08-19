import MathlibPlus.Open.Research.FormalizationBatch.K0104Claim8572

namespace MathlibPlus.Open.Research.FormalizationBatch.K0104Claim8578

open scoped BigOperators Interval
open MathlibPlus.Combinatorics.Claim8569
open MathlibPlus.Open.Research.FormalizationBatch.K0104Claim8581

noncomputable section

def positiveThermodynamicInterpolation_claim8578 : Prop :=
  ∀ (n m : ℕ) (x w : Fin n → ℝ),
    m ≤ n →
      StrictMono x →
        (∀ i : Fin n, 0 < x i) →
          (∀ i : Fin n, 0 < w i) →
            (∀ t : ℝ, 0 ≤ t → t ≤ 1 →
              (∀ i : Fin n,
                interpolatedHoleWeight8581 x w t i =
                  dualHoleWeight8581 x w i * Real.rpow (x i) (-t)) ∧
              (∀ H : Finset (Fin n), H ∈ holeSets8581 n m →
                holeProbability8581 (m := m) x
                    (interpolatedHoleWeight8581 x w t) H > 0) ∧
              (holeSets8581 n m).sum (fun H : Finset (Fin n) =>
                holeProbability8581 (m := m) x
                    (interpolatedHoleWeight8581 x w t) H) = 1 ∧
              (∀ H : Finset (Fin n), H ∈ holeSets8581 n m →
                logarithmicHoleStatistic8581 x H =
                  H.sum (fun i : Fin n => Real.log (x i))) ∧
              (partitionFunction n m x
                  (interpolatedHoleWeight8581 x w t) =
                partitionFunction n m x
                  (fun i => dualHoleWeight8581 x w i * Real.rpow (x i) (-t))))

end

end MathlibPlus.Open.Research.FormalizationBatch.K0104Claim8578
