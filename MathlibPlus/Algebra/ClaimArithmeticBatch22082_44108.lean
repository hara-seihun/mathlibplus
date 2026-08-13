import Mathlib

namespace MathlibPlus.Open.Algebra

/-- Claim 44108 under its literal same-affine-form reading.  The source
statement's displayed antisymmetry is retained verbatim as a Prop so that the
arithmetic check can expose any normalization mismatch. -/
def delta22ComplementAntisymmetry_claim44108 : Prop :=
  ∀ p cP cH : ℤ,
    7440 - 74 * (201 - p) + cH - cP =
      -(7440 - 74 * p + cP - cH)

end MathlibPlus.Open.Algebra

namespace MathlibPlus.Algebra.ClaimArithmeticBatch22082_44108

/-- Claim 22082: the displayed local degree parity chain. -/
theorem localDegreeParityIdentity_claim22082 (d a r B ε : ℕ)
    (h₁ : d ≡ a + r + B [MOD 2])
    (h₂ : a + r ≡ ε [MOD 2]) :
    d ≡ ε + B [MOD 2] := by
  exact h₁.trans (h₂.add_right B)

/-- The two affine defect functions in Claim 44108. -/
def delta20_claim44108 (p cP cH : ℤ) : ℤ :=
  7440 - 74 * p + cP - cH

def delta22_claim44108 (p cP cH : ℤ) : ℤ :=
  7440 - 74 * p + cP - cH

/-- Claim 44108: under the literal reading that both defects use the
same displayed affine formula, complementing `p` and swapping the correction
variables leaves a constant gap of `6` rather than giving the claimed negative.
This records the arithmetic boundary without silently changing either formula. -/
theorem delta22_complement_gap_claim44108 (p cP cH : ℤ) :
    delta22_claim44108 (201 - p) cH cP =
      -delta20_claim44108 p cP cH + 6 := by
  simp [delta20_claim44108, delta22_claim44108]
  ring_nf

/-- The literal same-formula antisymmetry in Claim 44108 is inconsistent with
its displayed constants; this is a disproof of that literal formal reading,
not a silent repair of the source formula. -/
theorem not_delta22ComplementAntisymmetry_claim44108 :
    ¬ MathlibPlus.Open.Algebra.delta22ComplementAntisymmetry_claim44108 := by
  intro h
  have h0 := h 0 0 0
  norm_num at h0

end MathlibPlus.Algebra.ClaimArithmeticBatch22082_44108
