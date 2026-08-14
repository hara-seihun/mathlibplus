import Mathlib

open scoped Interval BigOperators

namespace MathlibPlus.Open.Research.FormalizationBatchFeshbach

/-- Strict positivity of a real operator, expressed through its quadratic form. -/
def positiveDefinite
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : E → E) : Prop :=
  ∀ ⦃x : E⦄, x ≠ 0 → 0 < inner ℝ (T x) x

/-- The hypotheses that make `P` a finite orthogonal projection. -/
def selfAdjoint
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A : E →ₗ[ℝ] E) : Prop :=
  ∀ x y, inner ℝ (A x) y = inner ℝ x (A y)

/-- The hypotheses that make `P` a finite orthogonal projection. -/
def finiteOrthogonalProjection
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P : E →ₗ[ℝ] E) : Prop :=
  (∀ x y, inner ℝ (P x) y = inner ℝ x (P y)) ∧
    (∀ x, P (P x) = P x) ∧
      FiniteDimensional ℝ (LinearMap.range P)

/-- Exact-action Gram/Feshbach identities and the stated integral formulas. -/
def claim_7481 : Prop :=
  (∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      (A P : E →ₗ[ℝ] E) (τ : ℝ),
      selfAdjoint A →
      finiteOrthogonalProjection P →
      0 < τ →
      let IminusP : E → E := fun x => x - P x
      let H : E → E := fun x => P (A (P x))
      let F : E → E := fun x => P (A (A (P x)))
      let G : E → E := fun x => F x - H (H x)
      (∀ x, G x = P (A (IminusP (A (P x))))) ∧
        ((∀ x,
            0 ≤ inner ℝ (IminusP (A (IminusP x))) x -
              τ * inner ℝ (IminusP x) x) →
          positiveDefinite (fun x => H x - (τ⁻¹) • G x) →
          positiveDefinite A)) ∧
    (∀ (x : ℝ) (k : ℕ),
      0 < x →
        (∫ y in (0 : ℝ)..1, y ^ k / (x + y)) =
          (Finset.sum (Finset.range k)
              (fun j => (-x) ^ j / (((k - j : ℕ) : ℝ)))) +
            (-x) ^ k * (Real.log (1 + x) - Real.log x)) ∧
    (∀ (k r : ℕ),
      (∫ u in (0 : ℝ)..1, u ^ k * (Real.log u) ^ r) =
        ((-1 : ℝ) ^ r * (Nat.factorial r : ℝ)) /
          (((k + 1 : ℕ) : ℝ) ^ (r + 1)))

end MathlibPlus.Open.Research.FormalizationBatchFeshbach
