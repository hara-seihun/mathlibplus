import Mathlib

namespace MathlibPlus.Open.FormalizationBatch.GenericPerturbations

noncomputable def denseGenericPerturbationsDistinctPairDistances : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    let PairIndex := {p : Fin n × Fin n // p.1 < p.2}
    let CollisionIndex := {q : PairIndex × PairIndex // q.1 ≠ q.2}
    let distanceSquared :=
      fun (A : Fin n × Fin 2 → ℝ) (p : PairIndex) =>
        ∑ c : Fin 2, (A (p.1.1, c) - A (p.1.2, c)) ^ 2
    let collisionSet :=
      fun (q : CollisionIndex) =>
        {A | distanceSquared A q.1.1 = distanceSquared A q.1.2}
    let properAlgebraicHypersurface :=
      fun (S : Set (Fin n × Fin 2 → ℝ)) =>
        ∃ f : MvPolynomial (Fin n × Fin 2) ℝ,
          f ≠ 0 ∧
            S = {A | MvPolynomial.eval A f = 0} ∧
              S ≠ Set.univ
    let allPairDistancesDistinct : Set (Fin n × Fin 2 → ℝ) :=
      {A | ∀ p q : PairIndex, p ≠ q → distanceSquared A p ≠ distanceSquared A q}
    (∀ q : CollisionIndex, properAlgebraicHypersurface (collisionSet q)) ∧
      Set.Finite (Set.univ : Set CollisionIndex) ∧
        interior (⋃ q : CollisionIndex, collisionSet q) = ∅ ∧
          Dense allPairDistancesDistinct

end MathlibPlus.Open.FormalizationBatch.GenericPerturbations
