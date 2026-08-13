import Mathlib

namespace MathlibPlus.Open.Analysis.Claim18371

/--
The transform-domain law in admitted claim 18371.  The source names the
signal transform `L` and scattering operator `S` but does not provide their
carrier definitions, so they are explicit parameters of this exact law.
-/
def scatteringTransformLaw_claim18371
    {Signal : Type*} (L : Signal → ℂ → ℂ) (S : Signal → Signal) : Prop :=
  ∀ (f : Signal) (z : ℂ),
    L (S f) z =
      ((Real.pi : ℂ) ^ z *
          Complex.Gamma (5 / 4 - z / 2) /
            Complex.Gamma (5 / 4 + z / 2)) *
        L f (-z)

end MathlibPlus.Open.Analysis.Claim18371
