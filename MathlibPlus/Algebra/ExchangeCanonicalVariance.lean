import MathlibPlus.Basic

namespace MathlibPlus.Algebra.ExchangeCanonical

/-!
Formalization of admitted claim 54081.  The additive homomorphism `L` is the
one-copy response, `w` is the signed datum `W`, and `L w ≠ 0` records the
nonzero variance response `V₅(W)`.  Exchange invariance is the equality
`L (-w) = L w`; additivity supplies the oddness used in the source argument.
-/

/-- Exchange invariance forces an odd additive response to vanish on `w`. -/
theorem noExchangeCanonicalOneCopy
    {W Z : Type*} [AddCommGroup W] [AddCommGroup Z] [IsAddTorsionFree Z]
    (L : W →+ Z) (w : W)
    (h_exchange : L (-w) = L w)
    (hV : L w ≠ 0) : False := by
  have h_eq : L w = -L w := h_exchange.symm.trans (by simp)
  have h_two : L w + L w = 0 := by
    calc
      L w + L w = (-L w) + L w := congrArg (fun z => z + L w) h_eq
      _ = 0 := neg_add_cancel _
  have h_zero : L w = 0 := by
    apply (nsmul_right_injective (M := Z) (n := 2) (by norm_num))
    simpa [two_nsmul] using h_two
  exact hV h_zero

end MathlibPlus.Algebra.ExchangeCanonical
