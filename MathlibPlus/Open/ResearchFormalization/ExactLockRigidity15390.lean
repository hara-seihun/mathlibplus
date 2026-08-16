import MathlibPlus.Algebra.Claim15385

namespace MathlibPlus.Open.ResearchFormalization

/-- Exact-lock rigidity on a connected component of the nonvanishing chart.
If the projective logarithmic derivative vanishes along a nontrivial arc in
that component, it vanishes on the whole component, while the projective
coordinate is constant and the two carriers are proportional by a nonzero
constant. -/
def exactLockRigidity_15390 : Prop :=
  ∀ (U : Set ℂ) (X D : ℂ → ℂ),
    IsOpen U →
    IsConnected U →
    AnalyticOnNhd ℂ X U →
    AnalyticOnNhd ℂ D U →
    let U_nonzero : Set ℂ :=
      {z : ℂ | z ∈ U ∧ X z ≠ 0 ∧ D z ≠ 0}
    let Pi : ℂ → ℂ := fun z => -X z / D z
    let omega : ℂ → ℂ := fun z => deriv X z / X z - deriv D z / D z
    ∀ z₀ : ℂ, z₀ ∈ U_nonzero →
      let C : Set ℂ := connectedComponentIn U_nonzero z₀
      (∃ (a b : ℝ) (γ : ℝ → ℂ),
        a < b ∧
        ContinuousOn γ (Set.Icc a b) ∧
        Set.InjOn γ (Set.Icc a b) ∧
        γ a ≠ γ b ∧
        (∀ t ∈ Set.Icc a b, γ t ∈ C) ∧
        (∀ t ∈ Set.Icc a b, omega (γ t) = 0)) →
        (∀ z ∈ C, omega z = 0) ∧
        (∃ p : ℂ, p ≠ 0 ∧ ∀ z ∈ C, Pi z = p) ∧
        (∃ c : ℂ, c ≠ 0 ∧ ∀ z ∈ C, D z = c * X z)

end MathlibPlus.Open.ResearchFormalization
