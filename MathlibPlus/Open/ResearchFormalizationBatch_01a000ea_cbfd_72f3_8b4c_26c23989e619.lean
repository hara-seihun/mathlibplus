import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch

private def character (k : ℕ) (z : ℂˣ) : ℂ :=
  (Finset.range (k + 1)).sum (fun r =>
    ((z ^ (Int.ofNat k - Int.ofNat (2 * r)) : ℂˣ) : ℂ))

def claim_7928_all_degree_character_decomposition : Prop :=
  ∀ k : ℕ, ∀ a b : ℂˣ,
    character k a * character k b =
      (Finset.range (k + 1)).sum (fun j =>
        character j (a * b) * character (k - j) (a / b)) -
      (Finset.range (k - 1)).sum (fun j =>
        character j (a * b) * character (k - 2 - j) (a / b))

private def sign (i : Fin 2) : ℤ :=
  if i = 0 then 1 else -1

noncomputable def claim_7918_mixed_local_hadamard_identity : Prop :=
  ∀ (y α : ℂˣ),
    PowerSeries.mk (fun k => character k y * character k α) =
      (1 - PowerSeries.X ^ 2) *
        PowerSeries.inv
          ((Finset.univ : Finset (Fin 2)).prod (fun i =>
            (Finset.univ : Finset (Fin 2)).prod (fun j =>
              1 - PowerSeries.C
                (((y ^ sign i * α ^ sign j : ℂˣ) : ℂ)) * PowerSeries.X)))

private noncomputable def product_series (N : ℕ) (x : Fin N → ℂ) : PowerSeries ℂ :=
  (Finset.univ : Finset (Fin N)).prod (fun ν =>
    PowerSeries.C 1 - PowerSeries.C (x ν) * PowerSeries.X)

private noncomputable def reciprocal_coefficient (N : ℕ) (x : Fin N → ℂ) (n : ℕ) : ℂ :=
  PowerSeries.coeff n (PowerSeries.inv (product_series N x))

private noncomputable def residue_coefficient (N : ℕ) (x : Fin N → ℂ) (ν : Fin N) : ℂ :=
  ((Finset.univ.filter (fun μ : Fin N => μ ≠ ν)).prod (fun μ =>
    (1 - x μ / x ν)⁻¹))

def claim_8407_reciprocal_finite_product_residues : Prop :=
  ∀ (N : ℕ) (x : Fin N → ℂ),
    0 < N →
    (∀ ν, x ν ≠ 0) →
    (∀ ν μ, ν ≠ μ → x ν ≠ x μ) →
    let F : ℂ → ℂ := fun z =>
      (Finset.univ : Finset (Fin N)).prod (fun ν => 1 + x ν * z)
    let H : PowerSeries ℂ := PowerSeries.inv (product_series N x)
    let h : ℕ → ℂ := reciprocal_coefficient N x
    let c : Fin N → ℂ := residue_coefficient N x
    H = (Finset.univ : Finset (Fin N)).sum (fun ν =>
      PowerSeries.C (c ν) *
        PowerSeries.inv (PowerSeries.C 1 - PowerSeries.C (x ν) * PowerSeries.X)) ∧
    (∀ t : ℂ,
      F (-t) ≠ 0 →
      (1 / F (-t)) =
        (Finset.univ : Finset (Fin N)).sum (fun ν =>
          c ν / (1 - x ν * t))) ∧
    (∀ n : ℕ,
      (Finset.univ : Finset (Fin N)).sum (fun ν => c ν * (x ν) ^ n) = h n) ∧
    (∀ n : ℤ,
      (-N : ℤ) < n → n < 0 →
        (Finset.univ : Finset (Fin N)).sum (fun ν => c ν * (x ν) ^ n) = 0)

private def finite_trigonometric_sum
    (frequencies : Finset ℂ) (coefficients : ℂ → ℂ) (n : ℕ) : ℂ :=
  frequencies.sum (fun ω => coefficients ω * ω ^ n)

private def real_trigonometric_sum
    (frequencies : Finset ℂ) (coefficients : ℂ → ℂ) (n : ℕ) : ℝ :=
  (finite_trigonometric_sum frequencies coefficients n).re

private noncomputable def cesaro_mean (sequence : ℕ → ℝ) (N : ℕ) : ℝ :=
  ((N + 1 : ℕ) : ℝ)⁻¹ * (Finset.range (N + 1)).sum sequence

private noncomputable def cesaro_mean_square (sequence : ℕ → ℝ) (N : ℕ) : ℝ :=
  ((N + 1 : ℕ) : ℝ)⁻¹ *
    (Finset.range (N + 1)).sum (fun n => sequence n ^ 2)

def claim_8021_finite_nonconstant_trigonometric_sums_have_both_signs : Prop :=
  ∀ (frequencies : Finset ℂ) (coefficients : ℂ → ℂ),
    frequencies.Nonempty →
    (∀ ω ∈ frequencies,
      ‖ω‖ = 1 ∧ ω ≠ 1 ∧ coefficients ω ≠ 0) →
    (∀ n : ℕ, (finite_trigonometric_sum frequencies coefficients n).im = 0) →
    let T : ℕ → ℝ := real_trigonometric_sum frequencies coefficients
    let energy : ℝ :=
      frequencies.sum (fun ω => Complex.normSq (coefficients ω))
    Filter.Tendsto (cesaro_mean T) Filter.atTop (nhds 0) ∧
      Filter.Tendsto (cesaro_mean_square T) Filter.atTop (nhds energy) ∧
      0 < energy ∧
      (∃ bound : ℝ, ∀ n : ℕ, |T n| ≤ bound) ∧
      (∃ epsPos : ℝ, 0 < epsPos ∧
        ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ epsPos ≤ T n) ∧
      (∃ epsNeg : ℝ, 0 < epsNeg ∧
        ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ T n ≤ -epsNeg)

end MathlibPlus.Open.ResearchFormalizationBatch
