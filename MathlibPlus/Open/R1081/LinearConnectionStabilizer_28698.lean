import MathlibPlus.Open.R1081.FactorGraphs_01a000db_a016_792b_b33f_00a9410f47c6

namespace MathlibPlus.Open.R1081

private def triangularLinear (L : (Z7 × Z7) ≃ₗ[Z7] (Z7 × Z7)) : Prop :=
  ∃ a d c : Z7,
    (a = 1 ∨ a = -1) ∧
    (d = 1 ∨ d = -1) ∧
    ∀ x y : Z7, L (x, y) = (a * x, c * x + d * y)

private def linearStabilizer (Q I : Set Z7) :=
  {L : (Z7 × Z7) ≃ₗ[Z7] (Z7 × Z7) //
    Set.image (fun p : Z7 × Z7 => L p) (kernelConnectionSet Q I) =
      kernelConnectionSet Q I}

/-- Claim 28698: every linear stabilizer of one of the four displayed
connection sets is exactly the order-28 triangular subgroup. -/
def claim28698 : Prop :=
  ∀ Q I : Set Z7, admissibleQI Q I →
    (∀ L : (Z7 × Z7) ≃ₗ[Z7] (Z7 × Z7),
      (Set.image (fun p : Z7 × Z7 => L p) (kernelConnectionSet Q I) =
        kernelConnectionSet Q I ↔
        triangularLinear L)) ∧
    Nat.card (linearStabilizer Q I) = 28

end MathlibPlus.Open.R1081
