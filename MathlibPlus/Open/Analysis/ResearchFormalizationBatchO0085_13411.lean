import MathlibPlus.Open.Analysis.PrimeDepthLocalNormEscape

open MeasureTheory

namespace MathlibPlus.Open.Analysis.FormalizationBatchO0085

noncomputable section

/-- The finite weighted square energy from Claim 13411, with the reviewed
finite-prime-depth kernel carrier.  The definition is used on `c > 0` as in
the admitted statement. -/
noncomputable def finiteEnergy13411 (y : ℕ) (c : ℝ) : ℝ :=
  MeasureTheory.integral
    (volume.restrict (Set.Ioi (0 : ℝ)))
    (fun x =>
      |MathlibPlus.Open.Analysis.finitePrimeDepthKernel y x| ^ (2 : ℕ) *
        Real.rpow x (2 * c - 1))

/-- The all-prime weighted square energy from Claim 13411, with the reviewed
all-prime kernel carrier.  The definition is used on `c > 0` as in the
admitted statement. -/
noncomputable def allPrimeEnergy13411 (c : ℝ) : ℝ :=
  MeasureTheory.integral
    (volume.restrict (Set.Ioi (0 : ℝ)))
    (fun x =>
      |MathlibPlus.Open.Analysis.allPrimeKernel x| ^ (2 : ℕ) *
        Real.rpow x (2 * c - 1))

end
end MathlibPlus.Open.Analysis.FormalizationBatchO0085
