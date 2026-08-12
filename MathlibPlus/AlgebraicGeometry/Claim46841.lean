import MathlibPlus.Basic

namespace MathlibPlus.AlgebraicGeometry

/--
The exact arithmetic consequence in admitted claim 46841.  The source supplies
`c₁² = K² = 3`, `χ = 1 - q + p_g` with `p_g = 1` and `q = 0`, and Noether's
formula in the rearranged form `c₂ = 12χ - c₁²`.  No surface object is present
in the source ledger, so those displayed invariant equations are the formal
interface here.
-/
theorem chernSecondNumber_claim46841
    (c₁sq Ksq χ p_g q c₂ : ℚ)
    (h_c₁sq : c₁sq = Ksq)
    (h_Ksq : Ksq = 3)
    (h_χ : χ = 1 - q + p_g)
    (h_pg : p_g = 1)
    (h_q : q = 0)
    (h_noether : c₂ = 12 * χ - c₁sq) :
    c₂ = 21 := by
  rw [h_noether, h_χ, h_pg, h_q, h_c₁sq, h_Ksq]
  norm_num

end MathlibPlus.AlgebraicGeometry
