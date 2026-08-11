import Mathlib

/-!
# Reciprocal coefficient series

Exact algebraic material from packet `D-0013`: the reciprocal convolution, its first
three coefficient identities, and the packet's normalized pole-amplitude sign
convention.  No analytic assertion about poles or residues is made here.
-/

namespace MathlibPlus.Algebra.ReciprocalSeries

open scoped BigOperators

/-- The degree-`n` coefficient of `E(-t) H(t)`. -/
def reciprocalConvolution {R : Type*} [CommRing R]
    (e h : ℕ → R) (n : ℕ) : R :=
  ∑ i ∈ Finset.range (n + 1), (-1 : R) ^ i * e i * h (n - i)

/-- Coefficient-level statement that `E(-t) H(t) = 1`, including both constant
coefficients explicitly. -/
def IsReciprocalSeries {R : Type*} [CommRing R] (e h : ℕ → R) : Prop :=
  e 0 = 1 ∧ h 0 = 1 ∧
    ∀ n : ℕ, 0 < n → reciprocalConvolution e h n = 0

/-- The first three complete coefficients determined by the reciprocal relation. -/
theorem firstThree {R : Type*} [CommRing R] (e h : ℕ → R)
    (hs : IsReciprocalSeries e h) :
    h 1 = e 1 ∧
      h 2 = e 1 ^ 2 - e 2 ∧
      h 3 = e 1 ^ 3 - 2 * e 1 * e 2 + e 3 := by
  rcases hs with ⟨he0, hh0, hconv⟩
  have hconv1 := hconv 1 (by omega)
  have hconv2 := hconv 2 (by omega)
  have hconv3 := hconv 3 (by omega)
  norm_num [reciprocalConvolution, he0, hh0, Finset.sum_range_succ] at hconv1 hconv2 hconv3
  have hh1 : h 1 = e 1 := by
    linear_combination hconv1
  have hh2 : h 2 = e 1 ^ 2 - e 2 := by
    rw [hh1] at hconv2
    linear_combination hconv2
  have hh3 : h 3 = e 1 ^ 3 - 2 * e 1 * e 2 + e 3 := by
    rw [hh1, hh2] at hconv3
    linear_combination hconv3
  exact ⟨hh1, hh2, hh3⟩

/-- The fixed normalization `c = -residue / α` for a pole at `α`. -/
noncomputable def normalizedPoleAmplitude (alpha residue : ℝ) : ℝ :=
  -residue / alpha

/-- Multiplying the normalized amplitude by a nonzero pole location recovers the
negative residue. -/
theorem normalizedPoleAmplitude_mul (alpha residue : ℝ) (halpha : alpha ≠ 0) :
    normalizedPoleAmplitude alpha residue * alpha = -residue := by
  simp [normalizedPoleAmplitude, halpha]

/-- At a positive pole location, the packet's normalized amplitude has sign opposite
to the residue. -/
theorem normalizedPoleAmplitude_signs (alpha residue : ℝ) (halpha : 0 < alpha) :
    (0 < normalizedPoleAmplitude alpha residue ↔ residue < 0) ∧
      (normalizedPoleAmplitude alpha residue < 0 ↔ 0 < residue) := by
  have hmul := normalizedPoleAmplitude_mul alpha residue (ne_of_gt halpha)
  constructor
  · constructor
    · intro hamp
      have : 0 < normalizedPoleAmplitude alpha residue * alpha := mul_pos hamp halpha
      linarith
    · intro hresidue
      simpa [normalizedPoleAmplitude] using div_pos (neg_pos.mpr hresidue) halpha
  · constructor
    · intro hamp
      have : normalizedPoleAmplitude alpha residue * alpha < 0 :=
        mul_neg_of_neg_of_pos hamp halpha
      linarith
    · intro hresidue
      have hnegative : -residue < 0 := by linarith
      simpa [normalizedPoleAmplitude] using div_neg_of_neg_of_pos hnegative halpha

end MathlibPlus.Algebra.ReciprocalSeries
