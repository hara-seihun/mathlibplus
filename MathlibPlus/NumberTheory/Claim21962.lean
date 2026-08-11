import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace MathlibPlus.NumberTheory.Claim21962

/-- The integer equation in claim 21962 has a single progression once one
Bezout solution is chosen. -/
theorem allSolutions_progression {p q cstar fstar c f : ℤ}
    (hp : 0 < p) (hbase : p * cstar - q * fstar = 1)
    (hsol : p * c - q * f = 1) (hcop : IsCoprime p q) :
    ∃ ℓ : ℤ, c = cstar + q * ℓ ∧ f = fstar + p * ℓ := by
  have hdiff : p * (c - cstar) = q * (f - fstar) := by
    linear_combination hsol - hbase
  have hp0 : p ≠ 0 := ne_of_gt hp
  have hpdvd : p ∣ q * (f - fstar) := by
    rw [← hdiff]
    exact dvd_mul_right p (c - cstar)
  have hfdvd : p ∣ f - fstar := hcop.dvd_of_dvd_mul_left hpdvd
  obtain ⟨ℓ, hℓ⟩ := hfdvd
  refine ⟨ℓ, ?_, ?_⟩
  · have hcancel : p * (c - cstar) = p * (q * ℓ) := by
      calc
        p * (c - cstar) = q * (f - fstar) := hdiff
        _ = q * (p * ℓ) := by rw [hℓ]
        _ = p * (q * ℓ) := by ring
    have hcminus : c - cstar = q * ℓ := by
      exact mul_left_cancel₀ hp0 hcancel
    linarith
  · linarith [hℓ]

/-- Claim 21962, with the source's top-octant and interval conventions made
explicit.  The proof keeps the base Bezout pair independent of `R`. -/
theorem diophantineSolutionsFormOneProgression :
    ∀ (p q : ℤ),
      0 < p → 0 < q → IsCoprime p q →
        ∃ (cstar fstar : ℤ),
          p * cstar - q * fstar = 1 ∧
            ∀ (R : ℝ) (c f : ℤ),
              (p * c - q * f = 1 ∧
                7 * R / 8 ≤ (f : ℝ) ∧ (f : ℝ) ≤ R) ↔
                ∃! ℓ : ℤ,
                  c = cstar + q * ℓ ∧
                    f = fstar + p * ℓ ∧
                      7 * R / 8 ≤ ((fstar + p * ℓ : ℤ) : ℝ) ∧
                        ((fstar + p * ℓ : ℤ) : ℝ) ≤ R := by
  intro p q hp _hq hcop
  rcases hcop with ⟨a, b, hab⟩
  refine ⟨a, -b, ?_, ?_⟩
  · calc
      p * a - q * (-b) = a * p + b * q := by ring
      _ = 1 := hab
  · intro R c f
    constructor
    · rintro ⟨hsol, hlo, hhi⟩
      have hbase : p * a - q * (-b) = 1 := by
        calc
          p * a - q * (-b) = a * p + b * q := by ring
          _ = 1 := hab
      obtain ⟨ℓ, hc, hf⟩ := allSolutions_progression hp hbase hsol
        ⟨a, b, hab⟩
      refine ⟨ℓ, ⟨hc, hf, ?_, ?_⟩, ?_⟩
      · simpa [hf] using hlo
      · simpa [hf] using hhi
      · intro m hm
        have hfm : f = -b + p * m := hm.2.1
        have hfl : f = -b + p * ℓ := hf
        have hmul : p * m = p * ℓ := by linarith
        exact mul_left_cancel₀ (ne_of_gt hp) hmul
    · rintro ⟨ℓ, ⟨hc, hf, hlo, hhi⟩, _⟩
      refine ⟨?_, ?_, ?_⟩
      · calc
          p * c - q * f = p * (a + q * ℓ) - q * (-b + p * ℓ) := by rw [hc, hf]
          _ = p * a - q * (-b) := by ring
          _ = 1 := by
            calc
              p * a - q * (-b) = a * p + b * q := by ring
              _ = 1 := hab
      · simpa [hf] using hlo
      · simpa [hf] using hhi

end MathlibPlus.NumberTheory.Claim21962
