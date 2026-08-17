import MathlibPlus.Open.NumberTheory.Claim9192

namespace MathlibPlus.Open.NumberTheory.Claim9189

noncomputable section

/-- A replication-one exterior orbit gives a Mahler fixed point. -/
def disjointExteriorOrbitsGiveMahlerFixedPoint : Prop :=
  ∀ α : ℂ,
    MathlibPlus.Open.NumberTheory.Claim9192.admissible α →
      ∃ β : ℝ,
        β = MathlibPlus.Open.NumberTheory.Claim9192.mahlerMeasure α ∧
          ((β : ℂ) =
              MathlibPlus.Open.NumberTheory.Claim9192.exteriorProduct α ∨
            (β : ℂ) =
              -MathlibPlus.Open.NumberTheory.Claim9192.exteriorProduct α) ∧
          (∀ z ∈
              MathlibPlus.Open.NumberTheory.Claim9192.conjugateRoots (β : ℂ),
            z ≠ (β : ℂ) → ‖z‖ ≤ 1) ∧
          MathlibPlus.Open.NumberTheory.Claim9192.mahlerMeasure (β : ℂ) = β

end

end MathlibPlus.Open.NumberTheory.Claim9189
