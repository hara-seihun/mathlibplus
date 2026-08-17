import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0150Claim18318

noncomputable section
open scoped BigOperators

/-- Indices for positive real atoms, negative real atoms, and conjugate pairs. -/
abbrev DivisorIndex (rPlus rMinus q : ℕ) :=
  (Fin rPlus ⊕ Fin rMinus) ⊕ (Fin q × Bool)

/-- The orientation sign attached to the finite signed divisor. -/
def divisorSign {rPlus rMinus q : ℕ}
    (pairSign : Fin q → ℝ) :
    DivisorIndex rPlus rMinus q → ℝ
  | Sum.inl (Sum.inl _) => 1
  | Sum.inl (Sum.inr _) => -1
  | Sum.inr (a, _) => pairSign a

/-- Signed reciprocal-divisor moments. -/
noncomputable def signedReciprocalMoment
    {rPlus rMinus q : ℕ}
    (pairSign : Fin q → ℝ)
    (atoms : DivisorIndex rPlus rMinus q → ℂ) (n : ℕ) : ℂ :=
  ∑ a, (divisorSign pairSign a : ℂ) * (atoms a)⁻¹ ^ (n + 1)

/-- The real finite Hankel matrix cut from the conjugation-symmetric moments. -/
noncomputable def divisorHankel
    {rPlus rMinus q : ℕ}
    (pairSign : Fin q → ℝ)
    (atoms : DivisorIndex rPlus rMinus q → ℂ) (N : ℕ) :
    Matrix (Fin N) (Fin N) ℝ :=
  fun i j => (signedReciprocalMoment pairSign atoms (i.val + j.val)).re

/-- A quadratic form has a negative square when it has a negative vector. -/
def hasNegativeSquare {N : ℕ}
    (M : Matrix (Fin N) (Fin N) ℝ) : Prop :=
  ∃ v : Fin N → ℝ,
    ∑ i : Fin N, ∑ j : Fin N, v i * M i j * v j < 0

/-- The radius norm of a real test polynomial used in the finite-rank bound. -/
def polynomialRadiusNorm (p : Polynomial ℝ) (r : ℝ) : ℝ :=
  Finset.sum p.support (fun n => |p.coeff n| * r ^ n)

/-- The contribution of one conjugate pair to the real Hankel quadratic of a
real test polynomial. -/
noncomputable def pairHankelQuadratic
    {rPlus rMinus q : ℕ}
    (pairSign : Fin q → ℝ)
    (atoms : DivisorIndex rPlus rMinus q → ℂ)
    (a : Fin q) (p : Polynomial ℝ) : ℝ :=
  let lam : ℂ := atoms (Sum.inr (a, false))
  2 * ((pairSign a : ℂ) * lam⁻¹ *
      (p.eval₂ (algebraMap ℝ ℂ) lam⁻¹) ^ 2).re

/-- The reciprocal moment sequence of the controlled background after removing
both members of the selected conjugate pair. -/
noncomputable def backgroundMoment
    {rPlus rMinus q : ℕ}
    (pairSign : Fin q → ℝ)
    (atoms : DivisorIndex rPlus rMinus q → ℂ)
    (a : Fin q) (n : ℕ) : ℝ :=
  (∑ b : DivisorIndex rPlus rMinus q,
      if b = Sum.inr (a, false) ∨ b = Sum.inr (a, true) then
        0
      else
        (divisorSign pairSign b : ℂ) * (atoms b)⁻¹ ^ (n + 1)).re

/-- The exact real-atom and conjugate-pair shape of the divisor. -/
def realConjugateDivisor
    {rPlus rMinus q : ℕ}
    (atoms : DivisorIndex rPlus rMinus q → ℂ) : Prop :=
  (∀ a : Fin rPlus,
    (atoms (Sum.inl (Sum.inl a))).im = 0) ∧
    (∀ a : Fin rMinus,
      (atoms (Sum.inl (Sum.inr a))).im = 0) ∧
    (∀ a : Fin q,
      atoms (Sum.inr (a, true)) =
          starRingEnd ℂ (atoms (Sum.inr (a, false))) ∧
        (atoms (Sum.inr (a, false))).im ≠ 0) ∧
    (∀ a : DivisorIndex rPlus rMinus q, atoms a ≠ 0)

/-- Claim 18318: a nonreal conjugate divisor pair separated from its controlled
inner background, with a positive test margin, is visible in a finite Hankel
rank; the displayed logarithmic horizon is retained as a sufficient rank. -/
def everyHiddenNonrealPairEventuallyVisible18318 : Prop :=
  ∀ (rPlus rMinus q : ℕ)
    (pairSign : Fin q → ℝ)
    (atoms : DivisorIndex rPlus rMinus q → ℂ)
    (a : Fin q) (R r M δ : ℝ) (p : Polynomial ℝ),
    (∀ b : Fin q, pairSign b = 1 ∨ pairSign b = -1) →
    realConjugateDivisor atoms →
    0 < r → r < R →
    ‖atoms (Sum.inr (a, false))‖ = R →
    (∀ b : DivisorIndex rPlus rMinus q,
      b ≠ Sum.inr (a, false) → b ≠ Sum.inr (a, true) →
        ‖atoms b‖ < r) →
    0 < M → 0 < δ →
    pairHankelQuadratic pairSign atoms a p ≤ -δ →
    (∀ n : ℕ,
      |backgroundMoment pairSign atoms a n| ≤ M * r ^ (n + 1)) →
    ∀ k : ℕ,
      (k : ℝ) >
          Real.log (M * polynomialRadiusNorm p r ^ 2 / δ) /
            (2 * Real.log (R / r)) →
        hasNegativeSquare (divisorHankel pairSign atoms k)

end

end MathlibPlus.Open.ResearchFormalization.R0150Claim18318
