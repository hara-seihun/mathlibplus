import MathlibPlus.Basic

namespace MathlibPlus.Algebra

/--
The square-increment decomposition from claim 9235.  The packet uses `μ(d)` as
an increment of `M`; that convention is exposed as `hstep` rather than being
silently inferred from the displayed identity.
-/
theorem squareIncrementDecomposition_claim9235
    (M μ : ℕ → ℤ) (d : ℕ)
    (hstep : M d = M (d - 1) + μ d) :
    M d ^ 2 - M (d - 1) ^ 2 =
      2 * μ d * M (d - 1) + μ d ^ 2 := by
  rw [hstep]
  ring

end MathlibPlus.Algebra
