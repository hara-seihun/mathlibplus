import MathlibPlus.Open.LinearAlgebra.SupportSaturationFiniteCheck

namespace MathlibPlus.Open.LinearAlgebra.Claim5464

abbrev FiniteSignature (α : Type*) (d : ℕ) := α × (Fin d → ℕ)

private def signatureCarrier
    {K α Row : Type*} {d : ℕ} [Field K] [Fintype α]
    (S : GradedSparseSystem K α Row d) (h E : ℕ) :
    Set (FiniteSignature α d) :=
  {σ | ∃ c, c ∈ S.columns E ∧
    truncatedColumnSignature h c = σ}

/-- Claim 5464: for a fixed graded sparse system and radii `h ≤ s`, a
saturated local Morse certificate assigns positive waves, incident nonzero
row templates, strict descent on every other supported column, and the exact
truncated-support invariance under replacing a long coordinate by `s`. -/
def saturatedLocalMorseCertificate_claim5464
    {K α Row : Type*} {d : ℕ}
    [Field K] [Fintype α]
    (S : GradedSparseSystem K α Row d) (h s E : ℕ)
    (_h_le : h ≤ s) : Prop :=
  ∃ wave : FiniteSignature α d → ℕ,
    ∃ rowTemplate : FiniteSignature α d → Row,
      ∃ selected : FiniteSignature α d → GradedColumn α d,
        (∀ σ, σ ∈ signatureCarrier S h E →
          0 < wave σ ∧
            selected σ ∈ S.columns E ∧
              truncatedColumnSignature h (selected σ) = σ ∧
                rowTemplate σ ∈ S.rows E ∧
                  S.coefficient E (rowTemplate σ) (selected σ) ≠ 0 ∧
                    (∀ c, c ∈ rowSupport S E (rowTemplate σ) →
                      c ≠ selected σ →
                        wave (truncatedColumnSignature h c) < wave σ)) ∧
          (∀ σ, σ ∈ signatureCarrier S h E →
            ∀ c, c ∈ S.columns E →
              ∀ i : Fin d, s ≤ c.2 i →
                signatureSupportAt S h E (rowTemplate σ) =
                  signatureSupportAt S h
                    (S.grade (replaceColumnLength c i s))
                    (rowTemplate σ))

end MathlibPlus.Open.LinearAlgebra.Claim5464
