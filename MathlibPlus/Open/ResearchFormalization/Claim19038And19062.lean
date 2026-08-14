import Mathlib

namespace MathlibPlus.Open

/-- The positive two-atom cosine transform in claim 19038 has a genuinely
nonreal zero. -/
def claim19038_positiveCosineTransformHasNonrealZero : Prop :=
  0 < (1 : ℝ) ∧
    0 < (1 / 10 : ℝ) ∧
      ∃ z : ℂ,
        z.im ≠ 0 ∧
          Complex.cos z + (1 / 10 : ℂ) * Complex.cos (4 * z) = 0

/-- The complete zero lattice asserted for the explicit one-pair multiplier
in claim 19062. -/
def claim19062_onePairMultiplierExactZeroLattice : Prop :=
  ∀ (C L : ℝ),
    C > 1 →
      L > 0 →
        let Z : Set ℂ :=
          {z : ℂ |
            ∃ (k : ℤ) (ε : ℤ),
              (ε = -1 ∨ ε = 1) ∧
                z =
                  ((ε : ℂ) * (Real.arcosh C : ℂ) +
                    ((2 * k + 1 : ℤ) : ℂ) * (Real.pi : ℂ) * Complex.I) /
                    (L : ℂ)}
        (∀ z : ℂ, C + Complex.cosh ((L : ℂ) * z) = 0 ↔ z ∈ Z) ∧
          (∀ z : ℂ, z ∈ Z → z.re ≠ 0) ∧
          Set.Infinite Z ∧
          (∀ z : ℂ, z ∈ Z →
            star z ∈ Z ∧ -z ∈ Z ∧ -star z ∈ Z)

end MathlibPlus.Open
