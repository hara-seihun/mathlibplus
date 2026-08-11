import Mathlib

/-!
# Symmetric imaginary shifts
-/

namespace MathlibPlus.Analysis.SymmetricImaginaryShift

/-- The quadratic example attains the symmetric-shift strip-contraction
bound: after shifting by `±ia`, its only two roots have imaginary parts
`±√(Δ²-a²)`. -/
theorem quadratic_contractionSharp
    (u Δ a : ℝ) (ha : 0 ≤ a) (haΔ : a < Δ) :
    let F : ℂ → ℂ := fun z => (z - (u : ℂ)) ^ 2 + (Δ : ℂ) ^ 2
    let T : ℂ → ℂ := fun z =>
      F (z + Complex.I * (a : ℂ)) + F (z - Complex.I * (a : ℂ))
    let d := Real.sqrt (Δ ^ 2 - a ^ 2)
    (∀ z, T z =
        2 * ((z - (u : ℂ)) ^ 2 + (Δ : ℂ) ^ 2 - (a : ℂ) ^ 2)) ∧
      0 < d ∧
      (∀ z, T z = 0 ↔
        z = (u : ℂ) + Complex.I * (d : ℂ) ∨
        z = (u : ℂ) - Complex.I * (d : ℂ)) ∧
      (((u : ℂ) + Complex.I * (d : ℂ)).im = d ∧
        ((u : ℂ) - Complex.I * (d : ℂ)).im = -d) := by
  dsimp
  have hrad : 0 < Δ ^ 2 - a ^ 2 := by nlinarith
  have hd_sq : (Real.sqrt (Δ ^ 2 - a ^ 2)) ^ 2 = Δ ^ 2 - a ^ 2 :=
    Real.sq_sqrt hrad.le
  have hshift : ∀ z : ℂ,
      ((z + Complex.I * (a : ℂ) - (u : ℂ)) ^ 2 + (Δ : ℂ) ^ 2) +
          ((z - Complex.I * (a : ℂ) - (u : ℂ)) ^ 2 + (Δ : ℂ) ^ 2) =
        2 * ((z - (u : ℂ)) ^ 2 + (Δ : ℂ) ^ 2 - (a : ℂ) ^ 2) := by
    intro z
    ring_nf
    rw [show Complex.I ^ 2 = -1 by norm_num]
    ring
  constructor
  · exact hshift
  constructor
  · exact Real.sqrt_pos.2 hrad
  constructor
  · intro z
    have hrewrite :
        ((Δ : ℂ) ^ 2 - (a : ℂ) ^ 2) =
          (Real.sqrt (Δ ^ 2 - a ^ 2) : ℂ) ^ 2 := by
      exact_mod_cast hd_sq.symm
    have hcombine :
        (z - (u : ℂ)) ^ 2 + (Δ : ℂ) ^ 2 - (a : ℂ) ^ 2 =
          (z - (u : ℂ)) ^ 2 +
            (Real.sqrt (Δ ^ 2 - a ^ 2) : ℂ) ^ 2 := by
      calc
        _ = (z - (u : ℂ)) ^ 2 + ((Δ : ℂ) ^ 2 - (a : ℂ) ^ 2) := by ring
        _ = _ := by rw [hrewrite]
    have hi_sq :
        (Complex.I * (Real.sqrt (Δ ^ 2 - a ^ 2) : ℂ)) ^ 2 =
          -(Real.sqrt (Δ ^ 2 - a ^ 2) : ℂ) ^ 2 := by
      rw [mul_pow, show Complex.I ^ 2 = -1 by norm_num]
      ring
    rw [hshift z, mul_eq_zero]
    simp only [OfNat.ofNat_ne_zero, false_or]
    rw [hcombine]
    constructor
    · intro hz
      have hsquares :
          (z - (u : ℂ)) ^ 2 =
            (Complex.I * (Real.sqrt (Δ ^ 2 - a ^ 2) : ℂ)) ^ 2 := by
        rw [hi_sq]
        linear_combination hz
      rcases (sq_eq_sq_iff_eq_or_eq_neg.mp hsquares) with h | h
      · left; linear_combination h
      · right; linear_combination h
    · rintro (rfl | rfl)
      · ring_nf
        rw [show Complex.I ^ 2 = -1 by norm_num]
        ring
      · ring_nf
        rw [show Complex.I ^ 2 = -1 by norm_num]
        ring
  · norm_num

end MathlibPlus.Analysis.SymmetricImaginaryShift
