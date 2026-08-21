-- UNVERIFIED (native-decide): submitted but not kernel-verified, so it is not built and MathlibPlus.lean does not import it. See unverified.txt.
import Mathlib

namespace MathlibPlus.Algebra.ClaimIdentities

/-- Claim 13800: exact exponent gap and its consequence below `η = 1`. -/
theorem exactExponentGap (δ η : ℝ) :
    ((1 + δ - η) - (δ - 1) = 2 - η) ∧
      (η < 1 →
        ((1 + δ - η) - (δ - 1) > 1 ∧ δ - 1 < 1 + δ - η)) := by
  constructor
  · ring
  · intro hη
    constructor <;> linarith

/-- Claim 15660: the slope/rate pair recovers the squared height. -/
theorem slopeAndRateRecoverSquaredHeight (β γ d κ : ℝ)
    (hd : d = 1 / ((β - 1) ^ 2 + γ ^ 2))
    (hd0 : d ≠ 0)
    (hκ : κ = (2 * β - 1) * d) :
    γ ^ 2 = 1 / d - (1 - κ / d) ^ 2 / 4 := by
  have hden : (β - 1) ^ 2 + γ ^ 2 ≠ 0 := by
    intro hden
    rw [hden] at hd
    norm_num at hd
    exact hd0 hd
  have hprod : d * ((β - 1) ^ 2 + γ ^ 2) = 1 := by
    rw [hd]
    field_simp [hden]
  rw [hκ]
  field_simp [hd0]
  nlinarith [hprod]

/-- Claim 1427: exact target improvements in the historical claim.
Finite decimals are represented exactly in `ℚ`. -/
theorem exactTargetImprovements :
    let target : ℚ := 0.2043672
    let historical : ℚ := 0.1853
    let baseline : ℚ := 0.2043
    target - historical = 11917 / 625000 ∧
      target - baseline = 42 / 625000 := by
  norm_num

/-- Claim 11711: a symmetric two-way coupling contributes twice its squared
off-diagonal entry to the trace of the square. -/
theorem twoWayCouplingTrace (a e b : ℝ) :
    Matrix.trace ((!![a, e; e, b] : Matrix (Fin 2) (Fin 2) ℝ) ^ 2) =
      a ^ 2 + b ^ 2 + 2 * e ^ 2 := by
  simp [Matrix.trace, pow_two, Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- The trace contribution is strict when the coupling is nonzero. -/
theorem twoWayCouplingTrace_strict (a e b : ℝ) (he : e ≠ 0) :
    a ^ 2 + b ^ 2 <
      Matrix.trace ((!![a, e; e, b] : Matrix (Fin 2) (Fin 2) ℝ) ^ 2) := by
  rw [twoWayCouplingTrace]
  nlinarith [sq_pos_of_ne_zero he]

/-- Claim 11771: the two displayed coefficient vectors have the same positive
frequency-squared energy, while their frequency-squared traces have opposite
signs.  The unspecified scalar coefficient space is represented by `ℚ`. -/
theorem positiveHorizontalEnergy_not_signCoherent :
    let energy : ℚ × ℚ → ℚ := fun c => c.1 ^ 2 + 4 * c.2 ^ 2
    let trace : ℚ × ℚ → ℚ := fun c => c.1 + 4 * c.2
    energy (1, 1) = 5 ∧
      energy (1, -1) = 5 ∧
      trace (1, 1) = 5 ∧
      trace (1, -1) = -3 ∧
      0 < energy (1, 1) ∧
      0 < energy (1, -1) ∧
      0 < trace (1, 1) ∧
      trace (1, -1) < 0 := by
  norm_num

/-- Claim 13039: for `B > 2`, the displayed delayed-failure factor has the
three stated complex zeros. -/
theorem delayedFailureFactor_roots (B : ℝ) (_hB : 2 < B) :
    let d : ℝ := B ^ 2 + 1
    let F : ℂ → ℂ := fun z =>
      (1 + z / 2) *
        (1 + (2 * (B : ℂ) / (d : ℂ)) * z + z ^ 2 / (d : ℂ))
    ∀ z : ℂ,
      F z = 0 ↔
        z = -2 ∨ z = -(B : ℂ) + Complex.I ∨ z = -(B : ℂ) - Complex.I := by
  dsimp
  have hd : B ^ 2 + 1 ≠ 0 := by
    nlinarith [sq_nonneg B]
  intro z
  have hfirst : (1 + z / 2 = 0) ↔ z = -2 := by
    constructor
    · intro h
      linear_combination 2 * h
    · rintro rfl
      norm_num
  have hquad :
      (1 + (2 * (B : ℂ) / ((B ^ 2 + 1 : ℝ) : ℂ)) * z +
          z ^ 2 / ((B ^ 2 + 1 : ℝ) : ℂ) = 0) ↔
        z = -(B : ℂ) + Complex.I ∨ z = -(B : ℂ) - Complex.I := by
    have hdc : ((B ^ 2 + 1 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast hd
    have hfactor :
        1 + (2 * (B : ℂ) / ((B ^ 2 + 1 : ℝ) : ℂ)) * z +
            z ^ 2 / ((B ^ 2 + 1 : ℝ) : ℂ) =
          ((z + (B : ℂ) - Complex.I) * (z + (B : ℂ) + Complex.I)) /
            ((B ^ 2 + 1 : ℝ) : ℂ) := by
      field_simp [hdc]
      norm_num [Complex.ofReal_add, Complex.ofReal_pow]
      ring_nf
      simp only [Complex.I_sq]
      ring
    rw [hfactor]
    constructor
    · intro h
      rcases (div_eq_zero_iff.mp h) with hprod | hden
      · rcases mul_eq_zero.mp hprod with h₁ | h₂
        · left
          linear_combination h₁
        · right
          linear_combination h₂
      · exact False.elim (hdc hden)
    · rintro (h | h)
      · rw [h]
        apply (div_eq_zero_iff).2
        left
        ring
      · rw [h]
        apply (div_eq_zero_iff).2
        left
        ring
  rw [mul_eq_zero, hfirst, hquad]

/-- Claim 28481: ordered linearly independent pairs in `𝔽₃³` have the
advertised cardinality.  The displayed scalar-multiple criterion is the exact
`linearIndependent_fin2` normal form. -/
theorem orderedIndependentPairsF3_iff
    (p : (Fin 3 → ZMod 3) × (Fin 3 → ZMod 3)) :
    LinearIndependent (ZMod 3) ![p.1, p.2] ↔
      p.2 ≠ 0 ∧ ∀ a : ZMod 3, a • p.2 ≠ p.1 := by
  simpa using (linearIndependent_fin2 (K := ZMod 3)
    (V := Fin 3 → ZMod 3) (f := ![p.1, p.2]))

theorem orderedIndependentPairsF3 :
    Fintype.card
        {p : (Fin 3 → ZMod 3) × (Fin 3 → ZMod 3) //
          p.2 ≠ 0 ∧ ∀ a : ZMod 3, a • p.2 ≠ p.1} =
      (3 ^ 3 - 1) * (3 ^ 3 - 3) ∧
        (3 ^ 3 - 1) * (3 ^ 3 - 3) = 26 * 24 ∧
          26 * 24 = 624 := by
  native_decide


/-- Claim 24666: the displayed rooted-factor parallelogram polynomial expands
into the six monomials recorded by the source.  The rooted-tree factor
carriers are kept as an alignment boundary. -/
theorem rootedFactorParallelogram_normalForm_claim24666
    {R : Type*} [CommRing R] (z x₁ x₂ x₃ : R) :
    z * (x₁ * x₃ - x₂ ^ 2) + z ^ 2 * (x₁ * x₂ + x₃) -
        z ^ 3 * (x₁ ^ 2 + x₂) =
      z * x₁ * x₃ - z * x₂ ^ 2 + z ^ 2 * x₁ * x₂ + z ^ 2 * x₃ -
        z ^ 3 * x₁ ^ 2 - z ^ 3 * x₂ := by
  ring

end MathlibPlus.Algebra.ClaimIdentities
