import MathlibPlus.Open.ResearchFormalization.O0098Claim11428

noncomputable section

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.O0098Claim11426

open MathlibPlus.Open.ResearchFormalization.O0098Claim11428

/-- The finite reduced-residue count `C_Q(n)`. -/
def reducedResidueCount (Q n : ℕ) : ℕ :=
  (Finset.filter (fun m => Nat.gcd m Q = 1) (Finset.Icc 1 n)).card

/-- The reduced-residue discrepancy `D_Q(n)`. -/
def reducedResidueDiscrepancy (Q n : ℕ) : ℝ :=
  1 + (n : ℝ) * (Nat.totient Q : ℝ) / (Q : ℝ) -
    (reducedResidueCount Q n : ℝ)

/-- The weighted infinite discrepancy series, with the `n=0` term omitted. -/
def reducedResidueNormSeries (Q : ℕ) : ℝ :=
  ∑' n : ℕ,
    if 1 ≤ n then
      (reducedResidueDiscrepancy Q n) ^ 2 /
        ((n : ℝ) * ((n + 1 : ℕ) : ℝ))
    else 0

/-- Claim 11426: on each reciprocal interval the fractional-part basis and
primorial Nyman defect have the displayed reduced-residue values; the
resulting discrepancy is periodic modulo the primorial, and its squared L2
norm is the exact weighted series. -/
def claim11426_reducedResidueDiscrepancy : Prop :=
  ∀ y : ℕ,
    let Q := endpointPrimorial y
    (∀ (d n : ℕ) (x : ℝ),
      d ∈ Nat.divisors Q →
        1 ≤ n →
          1 / ((n + 1 : ℕ) : ℝ) < x →
            x < 1 / (n : ℝ) →
              endpointBasis (1 / (d : ℝ)) x =
                Int.fract ((n : ℝ) / (d : ℝ))) ∧
      (∀ (n : ℕ) (x : ℝ),
        1 ≤ n →
          1 / ((n + 1 : ℕ) : ℝ) < x →
            x < 1 / (n : ℝ) →
              endpointNymanG y x = reducedResidueDiscrepancy Q n) ∧
      (∀ n : ℕ,
        reducedResidueDiscrepancy Q (n + Q) =
          reducedResidueDiscrepancy Q n) ∧
      endpointNormSq y = reducedResidueNormSeries Q

end MathlibPlus.Open.ResearchFormalization.O0098Claim11426

end
