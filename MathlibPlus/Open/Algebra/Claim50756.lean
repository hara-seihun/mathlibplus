import MathlibPlus.Open.Algebra.Claim50758

namespace MathlibPlus.Open.Algebra.Claim50756

noncomputable def characterValue (ρ : ℂ) : ℂ :=
  Complex.exp ((1 / 2 - ρ) * (Real.log 2 : ℂ))

def innerFactor (q : ℂ) : ℂ := (5 * q + 4) * (4 * q + 5)

def outerFactor (q : ℂ) : ℂ := (2 * q + 1) * (q + 2)

/-- The two inner Laurent-factor roots correspond to genuinely off-critical
strip parameters, while the outer factor is nonvanishing on the open strip. -/
def offCriticalRootsAndOuterNonvanishing : Prop :=
  (∀ q : ℂ,
    innerFactor q = 0 ↔ q = (-4 / 5 : ℂ) ∨ q = (-5 / 4 : ℂ)) ∧
    (∀ q : ℂ,
      outerFactor q = 0 ↔ q = (-1 / 2 : ℂ) ∨ q = (-2 : ℂ)) ∧
    (∃ ρ : ℂ,
      characterValue ρ = (-4 / 5 : ℂ) ∧
        0 < ρ.re ∧ ρ.re < 1 ∧
        ρ.re = 1 / 2 + Real.log (5 / 4) / Real.log 2 ∧
        ρ.re ≠ 1 / 2) ∧
    (∃ ρ : ℂ,
      characterValue ρ = (-5 / 4 : ℂ) ∧
        0 < ρ.re ∧ ρ.re < 1 ∧
        ρ.re = 1 / 2 - Real.log (5 / 4) / Real.log 2 ∧
        ρ.re ≠ 1 / 2) ∧
    (∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 →
      outerFactor (characterValue ρ) ≠ 0) ∧
    (∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 →
      (2 : ℝ) ^ (-(1 / 2 : ℝ)) < ‖characterValue ρ‖ ∧
        ‖characterValue ρ‖ < (2 : ℝ) ^ (1 / 2 : ℝ))

end MathlibPlus.Open.Algebra.Claim50756
