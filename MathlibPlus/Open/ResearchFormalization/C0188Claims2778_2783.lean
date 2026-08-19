import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.C0188Claims2778_2783

noncomputable section

/-- The exact strict improvements of the 4.80 denominator over 4.81 and
4.862. -/
def claim2778 : Prop :=
  (4.80 : ℝ) < 4.81 ∧
    4.81 - 4.80 = 0.01 ∧
      0 < (4.81 : ℝ) - 4.80 ∧
        (4.80 : ℝ) < 4.862 ∧
          4.862 - 4.80 = 0.062 ∧
            0 < (4.862 : ℝ) - 4.80

/-- The corrected logistic packet with its endpoint cancellation and exact
multiplicative identity. -/
def claim2780 : Prop :=
  ∀ (d a : ℝ), 0 < d → 0 < a →
    let lam : ℝ := d / (2 * a)
    let q : ℝ → ℝ := fun u =>
      (1 - lam + lam * Real.exp (-a * u)) /
        (1 + Real.exp (-d * u))
    q 0 = 1 / 2 ∧
      HasDerivAt q 0 0 ∧
        ∀ u : ℝ,
          (1 + Real.exp (-d * u)) * q u =
            1 - lam + lam * Real.exp (-a * u)

/-- The uncorrected logistic packet has the nonzero endpoint derivative d/4
when d is nonzero. -/
def claim2783 : Prop :=
  ∀ (d : ℝ),
    let qRaw : ℝ → ℝ := fun u => (1 + Real.exp (-d * u))⁻¹
    HasDerivAt qRaw (d / 4) 0 ∧
      (d ≠ 0 → d / 4 ≠ 0)

end

end MathlibPlus.Open.ResearchFormalization.C0188Claims2778_2783
