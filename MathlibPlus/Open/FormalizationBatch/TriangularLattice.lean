import Mathlib

namespace MathlibPlus.Open.FormalizationBatch.TriangularLattice

noncomputable def triangularLatticeLimitBipartiteContactGraph : Prop :=
  ∀ (a : ℝ) (u v : EuclideanSpace ℝ (Fin 2)),
    ‖u‖ = 1 →
      ‖v‖ = 1 →
        0 < @Inner.inner ℝ (EuclideanSpace ℝ (Fin 2)) _ u v →
          @Inner.inner ℝ (EuclideanSpace ℝ (Fin 2)) _ u v = a →
            a < 1 / 2 →
              let lattice : Set (EuclideanSpace ℝ (Fin 2)) :=
                {x | ∃ m n : ℤ, x = m • u + n • v}
              let latticePoint : ℤ × ℤ → EuclideanSpace ℝ (Fin 2) :=
                fun z => z.1 • u + z.2 • v
              let gridAdjacency : (ℤ × ℤ) → (ℤ × ℤ) → Prop :=
                fun z w =>
                  Int.natAbs (z.1 - w.1) + Int.natAbs (z.2 - w.2) = 1
              let gridGraph := SimpleGraph.fromRel gridAdjacency
              let covolume : ℝ := |u 0 * v 1 - u 1 * v 0|
              (∀ m n : ℤ,
                  ‖m • u + n • v‖ ^ 2 =
                    (m : ℝ) ^ 2 + (n : ℝ) ^ 2 +
                      2 * a * (m : ℝ) * (n : ℝ)) ∧
                (∀ m n : ℤ,
                    0 ≤ m * n →
                      (m : ℝ) ^ 2 + (n : ℝ) ^ 2 +
                          2 * a * (m : ℝ) * (n : ℝ) ≥
                        (m : ℝ) ^ 2 + (n : ℝ) ^ 2) ∧
                  (∀ m n : ℤ,
                      m * n < 0 →
                        (m : ℝ) ^ 2 + (n : ℝ) ^ 2 +
                              2 * a * (m : ℝ) * (n : ℝ) >
                            (m : ℝ) ^ 2 + (n : ℝ) ^ 2 -
                              |(m : ℝ) * (n : ℝ)| ∧
                          (m : ℝ) ^ 2 + (n : ℝ) ^ 2 -
                              |(m : ℝ) * (n : ℝ)| =
                            (|(m : ℝ)| - |(n : ℝ)|) ^ 2 +
                              |(m : ℝ) * (n : ℝ)| ∧
                          (|(m : ℝ)| - |(n : ℝ)|) ^ 2 +
                              |(m : ℝ) * (n : ℝ)| ≥ 1) ∧
                    (∀ x : EuclideanSpace ℝ (Fin 2),
                        x ∈ lattice → x ≠ 0 → 1 ≤ ‖x‖) ∧
                      {x : EuclideanSpace ℝ (Fin 2) |
                          x ∈ lattice ∧ x ≠ 0 ∧ ‖x‖ = 1} =
                        {u, -u, v, -v} ∧
                        Set.BijOn latticePoint Set.univ lattice ∧
                          (∀ z w : ℤ × ℤ,
                              ‖latticePoint z - latticePoint w‖ = 1 ↔
                                gridAdjacency z w) ∧
                            SimpleGraph.IsBipartite gridGraph ∧
                              (∀ z w : ℤ × ℤ,
                                  gridAdjacency z w →
                                    (Even (z.1 + z.2) ↔
                                      ¬Even (w.1 + w.2))) ∧
                                covolume = Real.sqrt (1 - a ^ 2) ∧
                                  Filter.Tendsto
                                    (fun b : ℝ => Real.sqrt (1 - b ^ 2))
                                    (nhdsWithin (1 / 2) (Set.Iio (1 / 2)))
                                    (nhds (Real.sqrt 3 / 2))

end MathlibPlus.Open.FormalizationBatch.TriangularLattice
