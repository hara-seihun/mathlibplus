import Mathlib

/-!
# Moving-exchange Möbius identity (claim 28804)

The source writes the rational function through named factors `Z`, `E`, `P`,
and `R`.  Their ambient analytic carrier is not supplied in the packet, so the
exact displayed rational identity is recorded over an arbitrary field.  The
factorization is proved before any analytic interpretation of the quotient.
-/

namespace MathlibPlus.Algebra.Claim28804

/-- The two displayed forms of the moving-exchange rational function agree. -/
theorem moving_exchange_identity_claim28804
    {K : Type*} [Field K]
    (f D a s : K) :
    ((f + a * D) * (2 * f + (s - 2 * a) * D)) /
        ((f - a * D) * (2 * f - (s - 2 * a) * D)) =
      (2 * (f ^ 2 - a ^ 2 * D ^ 2) + s * (D * (f + a * D))) /
        (2 * (f ^ 2 - a ^ 2 * D ^ 2) + s * (-D * (f - a * D))) := by
  have hden :
      2 * (f ^ 2 - a ^ 2 * D ^ 2) + s * (-D * (f - a * D)) =
        (f - a * D) * (2 * f - (s - 2 * a) * D) := by
    ring
  rw [hden]
  congr 1
  ring

end MathlibPlus.Algebra.Claim28804
