import MathlibPlus.Open.AdmittedBatch.Lehmer
import MathlibPlus.Open.Research.FormalizationBatch.R0455
import MathlibPlus.Open.Research.FormalizationBatch.R0455_Cyclotomic

namespace MathlibPlus.Open.ResearchFormalizationBatch

noncomputable section

/-- Neither a positive power substitution nor its signed version repairs the
fixed Lehmer polynomial's mod-two packet defect. -/
def claim21636 : Prop :=
  let L : Polynomial ℤ := MathlibPlus.Open.AdmittedBatch.lehmerPolynomial
  let L₂ : Polynomial (ZMod 2) := integerPolynomialModTwo L
  let Xℤ : Polynomial ℤ := Polynomial.X
  let powerSubstitution : ℕ → Polynomial (ZMod 2) := fun k =>
    integerPolynomialModTwo (L.comp (Xℤ ^ k))
  let signedSubstitution : ℕ → Polynomial (ZMod 2) := fun k =>
    integerPolynomialModTwo (L.comp (-(Xℤ ^ k)))
  ¬ rootOrderPacketComplete L₂ ∧
    (∀ k : ℕ, 1 ≤ k →
      ¬ rootOrderPacketComplete (powerSubstitution k) ∧
        ¬ rootOrderPacketComplete (signedSubstitution k) ∧
          signedSubstitution k = powerSubstitution k ∧
          (rootOrderPacketComplete (powerSubstitution k) →
            rootOrderPacketComplete L₂) ∧
          (rootOrderPacketComplete (signedSubstitution k) →
            rootOrderPacketComplete L₂))

end

end MathlibPlus.Open.ResearchFormalizationBatch
