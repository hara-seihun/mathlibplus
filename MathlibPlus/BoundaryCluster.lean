import Mathlib

/-!
# Boundary-cluster sign consequences

Finite algebraic consequences extracted from source record `C-0002`.  These results
isolate the independent-factor sign law and give a concrete witness that positivity
of a real polynomial's coefficients does not force the Taylor series of its logarithm
about zero to reach the unit circle.
-/

namespace MathlibPlus.BoundaryCluster

open scoped BigOperators

/-- Nonnegative independent factors have a nonpositive second logarithmic cluster.
The two displayed cluster-coordinate identities are hypotheses here; deriving them
from the formal logarithm of the product is a separate formal-power-series result. -/
theorem independentFactors_pairCluster
    {m : ℕ} (w : Fin m → ℝ) (c1 c2 : ℝ)
    (_hw : ∀ r, 0 ≤ w r)
    (hc1 : c1 = ∑ r, w r)
    (hc2 : c2 = -(1 / 2 : ℝ) * ∑ r, w r ^ 2) :
    c1 = ∑ r, w r ∧ c2 ≤ 0 := by
  refine ⟨hc1, ?_⟩
  rw [hc2]
  exact mul_nonpos_of_nonpos_of_nonneg (by norm_num)
    (Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-- A positive second cluster cannot be represented by independent nonnegative
Bernoulli/path factors. -/
theorem positivePairCluster_refutesIndependence
    (c2 : ℝ) (hc2 : 0 < c2) :
    ¬ ∃ (m : ℕ) (w : Fin m → ℝ),
      (∀ r, 0 ≤ w r) ∧
        c2 = -(1 / 2 : ℝ) * ∑ r, w r ^ 2 := by
  rintro ⟨m, w, hw, hrepr⟩
  have hnonpos : c2 ≤ 0 :=
    (independentFactors_pairCluster w (∑ r, w r) c2 hw rfl hrepr).2
  exact (not_lt_of_ge hnonpos) hc2

/-- Positive coefficients and positivity on the nonnegative real axis do not force
all complex zeros outside the open unit disk.  The witness is `1 + 2X`, whose zero
is `-1/2`. -/
theorem positiveCoefficients_doNotForce_logRadiusOne :
    ∃ P : Polynomial ℝ,
      (∀ k, 0 ≤ P.coeff k) ∧
      (∀ x : ℝ, 0 ≤ x → 0 < P.eval x) ∧
      ∃ z : ℂ, ‖z‖ < 1 ∧
        (P.map (algebraMap ℝ ℂ)).eval z = 0 := by
  let P : Polynomial ℝ := Polynomial.C 1 + Polynomial.C 2 * Polynomial.X
  refine ⟨P, ?_, ?_, ?_⟩
  · intro k
    simp only [P, map_one, Polynomial.coeff_add, Polynomial.coeff_C_mul,
      Polynomial.coeff_one, Polynomial.coeff_X]
    split_ifs <;> norm_num
  · intro x hx
    simp [P]
    linarith
  · refine ⟨-(1 / 2 : ℂ), ?_, ?_⟩
    · norm_num
    · simp [P]

end MathlibPlus.BoundaryCluster
