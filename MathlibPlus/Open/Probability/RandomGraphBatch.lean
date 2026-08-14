import Mathlib

namespace MathlibPlus.Open.Probability.FormalizationBatch

open Filter

noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

def chromaticFirstOrderScale (n : ℕ) : ℝ :=
  (n : ℝ) / (2 * (Real.log (n : ℝ) / Real.log 2))

def chromaticScaleEvent (ε : ℝ) (n : ℕ) (G : SimpleGraph (Fin n)) : Prop :=
  let s := chromaticFirstOrderScale n
  let χ : ℝ := (G.chromaticNumber.toNat : ℝ)
  (1 - ε) * s ≤ χ ∧ χ ≤ (1 + ε) * s

/-- Claim 16696: the first-order chromatic-number scale holds with high
probability for the uniform (equivalently G(n,1/2)) graph law. -/
def chromaticNumberFirstOrderScale : Prop :=
  ∀ ε : ℝ, 0 < ε →
    Tendsto
      (fun n =>
        (Fintype.card {G : SimpleGraph (Fin n) // chromaticScaleEvent ε n G} : ℝ) /
          (Fintype.card (SimpleGraph (Fin n)) : ℝ))
      atTop (nhds 1)

end
end MathlibPlus.Open.Probability.FormalizationBatch
