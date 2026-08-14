import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

noncomputable section

/-- The rational parameter and endpoint functions in Claim 28584. -/
def endpointDelta (c : ℚ) : ℚ := 1 + (c + c⁻¹) / 2

def endpointZ (f D : ℚ) : ℚ := ((f - D) / (f + D)) ^ 2

def endpointF (δ Z : ℚ) : ℚ := -Z * (δ * Z + 2 - δ) / ((δ - 2) * Z - δ)

def admissibleEndpointParameter (c : ℚ) : Prop :=
  c ≠ 0 ∧ c ≠ 1 ∧ c ≠ -1

/-- Claim 28584: the exceptional endpoint packet definition. -/
def exceptionalEndpointPacket : Prop :=
  ∀ (c f D : ℚ), admissibleEndpointParameter c →
    endpointDelta c = 1 + (c + c⁻¹) / 2 ∧
      endpointZ f D = ((f - D) / (f + D)) ^ 2 ∧
        endpointF (endpointDelta c) (endpointZ f D) =
          -endpointZ f D *
            (endpointDelta c * endpointZ f D + 2 - endpointDelta c) /
              ((endpointDelta c - 2) * endpointZ f D - endpointDelta c)

/-- Claim 28585: the canceled-node factorization, under all displayed
nonvanishing denominator conditions. -/
def exactCanceledNodeFactorization : Prop :=
  ∀ (c f D : ℚ), admissibleEndpointParameter c →
    f + D ≠ 0 →
    (endpointDelta c - 2) * endpointZ f D - endpointDelta c ≠ 0 →
    (f + D) ^ 2 * (f + c * D) * (f + c⁻¹ * D) ≠ 0 →
      endpointF (endpointDelta c) (endpointZ f D) =
        ((f - D) ^ 2 * (f - c * D) * (f - c⁻¹ * D)) /
          ((f + D) ^ 2 * (f + c * D) * (f + c⁻¹ * D))

end

end MathlibPlus.Open.ResearchFormalization
