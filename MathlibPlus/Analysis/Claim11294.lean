import Mathlib

namespace MathlibPlus.Analysis

/-- The two complex roots in the off-axis quartet from claim 11294. -/
noncomputable def pPlus_claim11294 (δ T : ℝ) : ℂ :=
  (δ + Complex.I * T) ^ 2

/-- The conjugate root paired with `pPlus_claim11294`. -/
noncomputable def pMinus_claim11294 (δ T : ℝ) : ℂ :=
  starRingEnd ℂ (pPlus_claim11294 δ T)

/-- The rational correction displayed in claim 11294. -/
noncomputable def correction_claim11294 (δ T x : ℝ) : ℂ :=
  4 * (δ : ℂ) ^ 2 * ((x : ℂ) - 3 * (T : ℂ) ^ 2 - (δ : ℂ) ^ 2) /
    (((x : ℂ) + (T : ℂ) ^ 2) *
      (((x : ℂ) + (T : ℂ) ^ 2 - (δ : ℂ) ^ 2) ^ 2 +
        4 * (δ : ℂ) ^ 2 * (T : ℂ) ^ 2))

lemma rationalPair_claim11294 (a b u : ℂ)
    (ha : a - b ≠ 0) (hb : a + b ≠ 0) (hu : u ≠ 0)
    (hab : a ^ 2 - b ^ 2 ≠ 0) :
    2 / (a - b) + 2 / (a + b) - 4 / u =
      4 * (a * u - a ^ 2 + b ^ 2) / (u * (a ^ 2 - b ^ 2)) := by
  field_simp [ha, hb, hu, hab]
  ring

/-- Replacing an off-axis quartet by an on-axis double pair has the exact
rational correction stated in claim 11294.  The identity is stated on the
natural nonvanishing domain of its logarithmic-derivative summands. -/
theorem quartetRepair_claim11294 {δ T x : ℝ}
    (_hT : T ≠ 0)
    (hp : (x : ℂ) - pPlus_claim11294 δ T ≠ 0)
    (hm : (x : ℂ) - pMinus_claim11294 δ T ≠ 0)
    (ha : (x : ℂ) + (T ^ 2 : ℂ) ≠ 0) :
    2 / ((x : ℂ) - pPlus_claim11294 δ T) +
        2 / ((x : ℂ) - pMinus_claim11294 δ T) -
        4 / ((x : ℂ) + (T ^ 2 : ℂ)) =
      correction_claim11294 δ T x := by
  have hconj :
      starRingEnd ℂ ((δ + Complex.I * T) ^ 2) =
        ((δ : ℂ) - Complex.I * T) ^ 2 := by
    simp [map_pow, map_add, map_mul, Complex.conj_ofReal]
    ring
  have hp' : (x : ℂ) - ((δ : ℂ) + Complex.I * T) ^ 2 ≠ 0 := by
    simpa [pPlus_claim11294] using hp
  have hm' : (x : ℂ) - ((δ : ℂ) - Complex.I * T) ^ 2 ≠ 0 := by
    have hm0 : (x : ℂ) - ((δ : ℂ) + -(Complex.I * T)) ^ 2 ≠ 0 := by
      simpa [pPlus_claim11294, pMinus_claim11294, map_pow, map_add,
        map_mul, Complex.conj_ofReal] using hm
    convert hm0 using 1 <;> ring
  let u : ℂ := (x : ℂ) + (T : ℂ) ^ 2
  let a : ℂ := u - (δ : ℂ) ^ 2
  let b : ℂ := 2 * Complex.I * (δ : ℂ) * (T : ℂ)
  have hleftp : (x : ℂ) - pPlus_claim11294 δ T = a - b := by
    simp [pPlus_claim11294, u, a, b]
    ring_nf
    simp [Complex.I_mul_I]
  have hleftm : (x : ℂ) - pMinus_claim11294 δ T = a + b := by
    simp only [pMinus_claim11294, pPlus_claim11294]
    rw [hconj]
    simp [u, a, b]
    ring_nf
    simp [Complex.I_mul_I]
  have hap : a - b ≠ 0 := by simpa [hleftp] using hp
  have ham : a + b ≠ 0 := by simpa [hleftm] using hm
  have hu : u ≠ 0 := by simpa [u] using ha
  have hab : a ^ 2 - b ^ 2 ≠ 0 := by
    intro hz
    apply hap
    have hprod : (a + b) * (a - b) = 0 := by
      calc
        (a + b) * (a - b) = a ^ 2 - b ^ 2 := by ring
        _ = 0 := hz
    exact (mul_eq_zero.mp hprod).resolve_left ham
  have hb_sq :
      (2 * Complex.I * (δ : ℂ) * (T : ℂ)) ^ 2 =
        -4 * (δ : ℂ) ^ 2 * (T : ℂ) ^ 2 := by
    calc
      (2 * Complex.I * (δ : ℂ) * (T : ℂ)) ^ 2 =
          4 * (Complex.I : ℂ) ^ 2 * (δ : ℂ) ^ 2 * (T : ℂ) ^ 2 := by ring
      _ = -4 * (δ : ℂ) ^ 2 * (T : ℂ) ^ 2 := by
        rw [show (Complex.I : ℂ) ^ 2 = -1 by norm_num]
        ring
  have hnum :
      4 * (a * u - a ^ 2 + b ^ 2) =
        4 * (δ : ℂ) ^ 2 * ((x : ℂ) - 3 * (T : ℂ) ^ 2 - (δ : ℂ) ^ 2) := by
    dsimp [u, a, b]
    rw [hb_sq]
    ring
  have hden :
      u * (a ^ 2 - b ^ 2) =
        ((x : ℂ) + (T : ℂ) ^ 2) *
          (((x : ℂ) + (T : ℂ) ^ 2 - (δ : ℂ) ^ 2) ^ 2 +
            4 * (δ : ℂ) ^ 2 * (T : ℂ) ^ 2) := by
    dsimp [u, a, b]
    rw [hb_sq]
    ring
  rw [hleftp, hleftm]
  rw [rationalPair_claim11294 a b u hap ham hu hab]
  rw [hnum, hden]
  rfl

end MathlibPlus.Analysis
