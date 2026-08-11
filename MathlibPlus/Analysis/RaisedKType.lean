import Mathlib

/-!
# Raised K-type local factor

The exact finite-product local factor from admitted claim 297.
-/

open scoped BigOperators

namespace MathlibPlus.Analysis.RaisedKType

/-- The raised K-type local factor
`β_{k,m}(s) = ∏_{0 ≤ r < m} (k + 2r + 1 - s) / (k + 2r + 1 + s)`.

The expression is defined for every real `k`; the packet uses it on the domain
`k > 0`. -/
noncomputable def beta (k : ℝ) (m : ℕ) (s : ℂ) : ℂ :=
  ∏ r ∈ Finset.range m,
    (((k + 2 * r + 1 : ℝ) : ℂ) - s) /
      (((k + 2 * r + 1 : ℝ) : ℂ) + s)

/-- On the packet's positive-weight domain, `beta` unfolds to the stated
finite product. -/
theorem beta_eq_product {k : ℝ} (_hk : 0 < k) (m : ℕ) (s : ℂ) :
    beta k m s =
      ∏ r ∈ Finset.range m,
        (((k + 2 * r + 1 : ℝ) : ℂ) - s) /
          (((k + 2 * r + 1 : ℝ) : ℂ) + s) := by
  rfl

/-- The lower shifted weight `A_r = k + 2r + 1/2`. -/
noncomputable def lowerShift (k : ℝ) (r : ℕ) : ℝ :=
  k + 2 * r + 1 / 2

/-- The upper shifted weight `B_r = k + 2r + 3/2`. -/
noncomputable def upperShift (k : ℝ) (r : ℕ) : ℝ :=
  k + 2 * r + 3 / 2

/-- The exact product denoted `ρ_m(t)^2` in the packet. -/
noncomputable def rhoSq (k : ℝ) (m : ℕ) (t : ℝ) : ℝ :=
  ∏ r ∈ Finset.range m,
    (lowerShift k r ^ 2 + t ^ 2) / (upperShift k r ^ 2 + t ^ 2)

/-- The accumulated phase
`ψ_m(t) = ∑_{r<m} (arctan (t/A_r) + arctan (t/B_r))`. -/
noncomputable def phase (k : ℝ) (m : ℕ) (t : ℝ) : ℝ :=
  ∑ r ∈ Finset.range m,
    (Real.arctan (t / lowerShift k r) +
      Real.arctan (t / upperShift k r))

/-- The total dyadic phase `Θ_m(t) = t log 2 + ψ_m(t)`. -/
noncomputable def totalPhase (k : ℝ) (m : ℕ) (t : ℝ) : ℝ :=
  t * Real.log 2 + phase k m t

/-- Exact simultaneous unfolding of the critical-line modulus-squared and
phase definitions from admitted claim 298. -/
theorem criticalLineModulusPhase {k : ℝ} (_hk : 0 < k) (m : ℕ) (t : ℝ) :
    rhoSq k m t =
        ∏ r ∈ Finset.range m,
          (lowerShift k r ^ 2 + t ^ 2) / (upperShift k r ^ 2 + t ^ 2) ∧
      phase k m t =
        ∑ r ∈ Finset.range m,
          (Real.arctan (t / lowerShift k r) +
            Real.arctan (t / upperShift k r)) ∧
      totalPhase k m t = t * Real.log 2 + phase k m t := by
  exact ⟨rfl, rfl, rfl⟩

end MathlibPlus.Analysis.RaisedKType
