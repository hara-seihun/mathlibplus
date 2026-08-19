import MathlibPlus.Open.Analysis.AdmittedResolventInertia10722

namespace MathlibPlus.Open.ResearchFormalization.O0057Claim10719

open scoped BigOperators

noncomputable section

open MathlibPlus.Open.Analysis

private def primeAtomMatrixGeneric10719 {M : ℕ}
    (a ell : ℝ) (rates : Fin M → ℝ) : Matrix (Fin M) (Fin M) ℝ :=
  (-2 * a) • Matrix.of (fun i j =>
    evenTranslationCorrelation ell (rates i) (rates j))

private def scalarInertiaRelation10719 {M : ℕ}
    (a ell : ℝ) (rates : Fin M → ℝ) (p n z : ℕ) : Prop :=
  (0 < -2 * a →
      hasInertia (primeAtomMatrixGeneric10719 a ell rates) p n z) ∧
    (-2 * a < 0 →
      hasInertia (primeAtomMatrixGeneric10719 a ell rates) n p z)

/-- Claim 10719: every positive translation length supports finite Gram matrices
with arbitrarily many positive and negative directions.  The exact
sign-dependent inertia transformation for each nonzero scalar prime atom is
included, so a negative scalar exchanges the positive and negative indices. -/
def claim10719_unboundedTwoSidedPrimeFiberInertia : Prop :=
  ∀ (ell : ℝ),
    0 < ell →
      ∀ (N : ℕ),
        1 ≤ N →
          ∃ (M : ℕ) (rates : Fin M → ℝ)
            (p n z : ℕ),
            N ≤ p ∧
              N ≤ n ∧
                (∀ i : Fin M, 1 / 2 < rates i) ∧
                  Function.Injective rates ∧
                    hasInertia
                        (Matrix.of (fun i j =>
                          evenTranslationCorrelation ell (rates i) (rates j)))
                        p n z ∧
                      (∀ a : ℝ, a ≠ 0 →
                        scalarInertiaRelation10719 a ell rates p n z)

end

end MathlibPlus.Open.ResearchFormalization.O0057Claim10719
