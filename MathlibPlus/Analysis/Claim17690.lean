import MathlibPlus.Basic

open MeasureTheory

namespace MathlibPlus.Analysis.Claim17690

/-!
The source defines the backward Green moment only for positive `λ`.  A positive
real subtype keeps that domain exact instead of extending the source object by
an unreviewed convention.
-/

/-- The backward Green moment from claim 17690. -/
noncomputable def backwardGreenMoment
    (r : ℕ) (lam : {x : ℝ // 0 < x}) : ℝ :=
  lam.1 ^ (-1 / 4 : ℝ) /
      (((2 : ℝ) ^ r) * (Nat.factorial r : ℝ)) *
    ∫ τ in Set.Ioi lam.1,
      Real.log (τ / lam.1) ^ r * τ ^ (-3 / 4 : ℝ) * Real.exp (-τ)

end MathlibPlus.Analysis.Claim17690
