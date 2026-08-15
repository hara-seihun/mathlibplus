import Mathlib

namespace MathlibPlus.Open.FormalizationBatch.DiameterRatio

noncomputable def logarithmicDiameterRatioDirectionalDerivative : Prop :=
  ∀ (n d : ℕ)
    (X w : Fin n → EuclideanSpace ℝ (Fin d)),
    2 ≤ n →
      let PairIndex := {p : Fin n × Fin n // p.1 < p.2}
      let distanceSquared :=
        fun (Y : Fin n → EuclideanSpace ℝ (Fin d)) (p : PairIndex) =>
          ‖Y p.1.1 - Y p.1.2‖ ^ 2
      (∀ p : PairIndex, 0 < distanceSquared X p) →
        let phi :=
          fun (Y : Fin n → EuclideanSpace ℝ (Fin d)) =>
            Real.log (sSup (Set.range (distanceSquared Y))) -
              Real.log (sInf (Set.range (distanceSquared Y)))
        let closest : Set PairIndex :=
          {p | distanceSquared X p = sInf (Set.range (distanceSquared X))}
        let farthest : Set PairIndex :=
          {p | distanceSquared X p = sSup (Set.range (distanceSquared X))}
        let ell :=
          fun (p : PairIndex) =>
            2 *
                @Inner.inner ℝ (EuclideanSpace ℝ (Fin d)) _
                  (X p.1.1 - X p.1.2) (w p.1.1 - w p.1.2) /
              distanceSquared X p
        Filter.Tendsto
          (fun t : ℝ =>
            (phi (fun i => X i + t • w i) - phi X) / t)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0))
          (nhds (sSup (ell '' farthest) - sInf (ell '' closest)))

end MathlibPlus.Open.FormalizationBatch.DiameterRatio
