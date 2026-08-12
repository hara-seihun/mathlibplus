import MathlibPlus.Basic

namespace MathlibPlus.Analysis

open scoped InnerProductSpace

/-!
Formalization of admitted claim 9740.  The source's gcd-kernel pairing is
represented by an arbitrary real inner-product space; `H_N` is its squared
norm and `w_N` is the increment in `u_N = u_(N-1) + w_N`.  These are the
structural interfaces used by the displayed energy identity, rather than
additional mathematical conclusions.
-/

/-- Energy increment under one additive update in a real inner-product space. -/
theorem energyIncrement_claim9740
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u w : ℕ → E) (H : ℕ → ℝ) (N : ℕ) (_hN : 1 ≤ N)
    (hH : ∀ k, H k = ‖u k‖ ^ 2)
    (hstep : u N = u (N - 1) + w N) :
    H N - H (N - 1) =
      2 * ⟪u (N - 1), w N⟫_ℝ + ‖w N‖ ^ 2 := by
  calc
    H N - H (N - 1) =
        ‖u N‖ ^ 2 - ‖u (N - 1)‖ ^ 2 := by rw [hH, hH]
    _ =
        ⟪u N, u N⟫_ℝ - ⟪u (N - 1), u (N - 1)⟫_ℝ := by
          rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
    _ = 2 * ⟪u (N - 1), w N⟫_ℝ + ‖w N‖ ^ 2 := by
      rw [hstep, real_inner_add_add_self, ← real_inner_self_eq_norm_sq]
      ring

end MathlibPlus.Analysis
