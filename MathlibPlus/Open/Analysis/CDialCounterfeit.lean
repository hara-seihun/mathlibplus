import MathlibPlus.Analysis.CDialCounterfeit

/-!
# c-dial transform formula

Registry statement for the packet's Fourier/Bessel identity. No proof is asserted here.
-/

namespace MathlibPlus.Open.Analysis.CDialCounterfeit

/-- For every packet parameter `c ≥ 1`, the Fourier transform of the `c`-dial source is the
stated linear combination of modified Bessel functions. -/
def transformFormula : Prop :=
  ∀ c : ℝ, 1 ≤ c → ∀ z : ℂ,
    MathlibPlus.Analysis.CDialCounterfeit.fourierTransform
        (MathlibPlus.Analysis.CDialCounterfeit.source c) z =
      MathlibPlus.Analysis.CDialCounterfeit.transformExpression c z

end MathlibPlus.Open.Analysis.CDialCounterfeit
