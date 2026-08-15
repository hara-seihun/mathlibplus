import Mathlib

namespace MathlibPlus.Open.Analysis

/-- The principal real branch of Lambert's W function, written directly on the
nonnegative branch used by the odd-index weights below. -/
noncomputable def principalLambertW (x : ℝ) : ℝ :=
  sInf {y : ℝ | 0 ≤ y ∧ x ≤ y * Real.exp y}

/-- `W_j = W₀(j/(2π))`. -/
noncomputable def lambertWeight (j : ℕ) : ℝ :=
  principalLambertW ((j : ℝ) / (2 * Real.pi))

/-- `R_j = log (8π a_j) + W_j`. -/
noncomputable def liftedGauge (a : ℕ → ℝ) (j : ℕ) : ℝ :=
  Real.log (8 * Real.pi * a j) + lambertWeight j

/-- `C_m = ell_m - ell_(m+1)`. -/
def chemicalPotentialFirstDifference (ell : ℕ → ℝ) (m : ℕ) : ℝ :=
  ell m - ell (m + 1)

/--
On growing blocks of odd indices, the odd additive Lambert condition is
 equivalent to the first-difference asymptotic, under the exact odd identity
 supplied by the mesh relation.
-/
def oddAdditiveLambertLawIffFirstDifference : Prop :=
  ∀ (a ell : ℕ → ℝ) (n : ℕ → ℕ) (K : ℕ → Finset ℕ),
    (hK : ∀ N, (K N).Nonempty) →
      Filter.Tendsto (fun N => (K N).min' (hK N)) Filter.atTop Filter.atTop →
      (∀ N k, k ∈ K N → 1 ≤ k ∧ k ≤ n N) →
      (∀ N k, k ∈ K N →
        liftedGauge a (2 * k - 1) =
          Real.log (8 * Real.pi) + lambertWeight (2 * k - 1) +
            (1 / 2 : ℝ) * chemicalPotentialFirstDifference ell (n N - k)) →
      ((Filter.Tendsto
          (fun N =>
            (K N).sup' (hK N)
              (fun k =>
                lambertWeight (2 * k - 1) *
                  |liftedGauge a (2 * k - 1)|))
          Filter.atTop (nhds 0)) ↔
        ∃ ε : ℕ → ℕ → ℝ,
          (∀ N k, k ∈ K N →
            chemicalPotentialFirstDifference ell (n N - k) =
              -2 * Real.log (8 * Real.pi) -
                2 * lambertWeight (2 * k - 1) + ε (n N) k) ∧
          Filter.Tendsto
            (fun N =>
              (K N).sup' (hK N)
                (fun k =>
                  lambertWeight (2 * k - 1) * |ε (n N) k|))
            Filter.atTop (nhds 0))

end MathlibPlus.Open.Analysis
