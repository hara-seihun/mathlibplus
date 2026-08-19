import MathlibPlus.Open.ResearchFormalization.R2614Claim42807

namespace MathlibPlus.Open.ResearchFormalization.R2614Claim42808

noncomputable section

open MathlibPlus.Open.ResearchFormalization.R2614Claims42815_42818
open MathlibPlus.Open.ResearchFormalization.R2614Claim42807

/-- Claim 42808: on the exact predecessor-supported index domain, the
fixed-offset determinant at rank `R` is obtained from the rank-`R-1`
determinant by applying one `1 + T_i` factor for every row coordinate. -/
def claim42808 : Prop :=
  ∀ (m R : ℕ) (offsets : Fin m → ℤ) (q : Fin m → ℤ),
    (1 ≤ R ∧
      ∀ i : Fin m, ∀ j : Fin m,
        recurrenceSupported R (q i) (offsets j)) →
      kernelMinorRows R offsets q =
        (applyIntRatOperators
          (Finset.univ.toList.map (fun i =>
            fun F : IntFunction m => F + intShiftOperator i F))
          (fun rows => kernelMinorRows (R - 1) offsets rows)) q

end

end MathlibPlus.Open.ResearchFormalization.R2614Claim42808
