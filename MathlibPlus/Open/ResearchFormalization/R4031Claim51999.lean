import MathlibPlus.Open.Research.R4031Claim51988

namespace MathlibPlus.Open.ResearchFormalization.R4031Claim51999

open scoped BigOperators
open MathlibPlus.Open.Research.R4031Claim51988

noncomputable section

abbrev BooleanLaw (n : ℕ) := Atom n → ℝ

def isProbabilityLaw {n : ℕ} (nu : BooleanLaw n) : Prop :=
  (∀ k, 0 ≤ nu k) ∧
    (∑ k : Atom n, nu k) = 1

noncomputable def lawExpectation {n : ℕ} (nu : BooleanLaw n)
    (f : Atom n → ℝ) : ℝ :=
  ∑ k : Atom n, nu k * f k

noncomputable def lawBarycentre {n : ℕ} (nu : BooleanLaw n) : Table n :=
  fun x => ∑ k : Atom n, nu k * atomValue k x

noncomputable def diracLaw {n : ℕ} (h : Atom n) : BooleanLaw n :=
  fun k => if k = h then 1 else 0

noncomputable def radialLaw {n : ℕ} (h : Atom n) (nu : BooleanLaw n)
    (beta : ℝ) : BooleanLaw n :=
  fun k => (1 - beta) * diracLaw h k + beta * nu k

noncomputable def radialPoint {n : ℕ} (h : Atom n) (nu : BooleanLaw n)
    (beta : ℝ) : Table n :=
  atomValue h + beta • (lawBarycentre nu - atomValue h)

noncomputable def lawAverageLoss {n : ℕ} (nu : BooleanLaw n)
    (policies : Atom n → QueryTree n) (u : Table n) : ℝ :=
  ∑ k : Atom n, nu k * policyLoss (policies k) u

noncomputable def lawAveragePair {n : ℕ} (nu : BooleanLaw n)
    (policies : Atom n → QueryTree n) (u w : Table n) : ℝ :=
  ∑ k : Atom n, nu k * policyPair (policies k) u w (fun _ => none)

noncomputable def radialScore {n : ℕ} (law : BooleanLaw n)
    (h : Atom n) : ℝ :=
  let u := lawBarycentre law
  constrainedLoss h u - queryCost h +
    lawExpectation law
      (fun k =>
        2 * constrainedPairing k u h - constrainedLoss k u - queryCost k)

def directionalActive {n : ℕ} (k : Atom n) (u : Table n)
    (h : Atom n) (policy : QueryTree n) : Prop :=
  constrainedActive k u policy ∧
    policyPair policy u (atomValue h) (fun _ => none) =
      constrainedPairing k u h

def radialTuple {n : ℕ} (nu : BooleanLaw n) (h : Atom n)
    (beta : ℝ) (Qh : QueryTree n) (Q : Atom n → QueryTree n) : Prop :=
  0 ≤ beta ∧ beta ≤ 1 ∧
    directionalActive h (radialPoint h nu beta) h Qh ∧
    ∀ k, directionalActive k (radialPoint h nu beta) h (Q k)

noncomputable def radialLinearCoefficient {n : ℕ}
    (nu : BooleanLaw n) (h : Atom n)
    (Qh : QueryTree n) (Q : Atom n → QueryTree n) : ℝ :=
  let d := lawBarycentre nu - atomValue h
  queryCost h - policyLoss Qh (atomValue h) +
    2 * policyPair Qh (atomValue h) d (fun _ => none) +
    lawAverageLoss nu Q (atomValue h) - lawExpectation nu queryCost

noncomputable def radialCubicCoefficient {n : ℕ}
    (nu : BooleanLaw n) (h : Atom n)
    (Qh : QueryTree n) (Q : Atom n → QueryTree n) : ℝ :=
  let d := lawBarycentre nu - atomValue h
  policyLoss Qh d - lawAverageLoss nu Q d

def realInterval (I : Set ℝ) : Prop :=
  ∀ ⦃x z : ℝ⦄, x ∈ I → z ∈ I →
    ∀ y : ℝ, x ≤ y → y ≤ z → y ∈ I

def positiveInteriorMaximum (f : ℝ → ℝ) (I : Set ℝ)
    (beta₀ : ℝ) : Prop :=
  0 < beta₀ ∧ beta₀ < 1 ∧ beta₀ ∈ I ∧ 0 < f beta₀ ∧
    ∃ epsilon : ℝ,
      0 < epsilon ∧
        Set.Icc (beta₀ - epsilon) (beta₀ + epsilon) ⊆ I ∧
        ∀ beta : ℝ, beta ∈ I → beta ≠ beta₀ →
          |beta - beta₀| < epsilon → f beta < f beta₀

noncomputable def policyProfileDerivativeDrop {n : ℕ}
    (left right : QueryTree n) (h : Atom n) (nu : BooleanLaw n)
    (beta₀ : ℝ) : ℝ :=
  derivWithin
      (fun beta => policyLoss left (radialPoint h nu beta))
      (Set.Iic beta₀) beta₀ -
    derivWithin
      (fun beta => policyLoss right (radialPoint h nu beta))
      (Set.Ici beta₀) beta₀

noncomputable def radialSwitchData {n : ℕ}
    (nu : BooleanLaw n) (h : Atom n) (beta₀ : ℝ) (I left right : Set ℝ)
    (QhLeft QhRight : QueryTree n)
    (QLeft QRight : Atom n → QueryTree n) : Prop :=
  isProbabilityLaw nu ∧
    realInterval I ∧
    0 < beta₀ ∧ beta₀ < 1 ∧ beta₀ ∈ I ∧
    left = I ∩ Set.Iio beta₀ ∧
    right = I ∩ Set.Ioi beta₀ ∧
    (∃ epsilon : ℝ,
      0 < epsilon ∧
        Set.Icc (beta₀ - epsilon) (beta₀ + epsilon) ⊆ I) ∧
    (∀ beta : ℝ, beta ∈ left →
      beta < beta₀ ∧ radialTuple nu h beta QhLeft QLeft) ∧
    (∀ beta : ℝ, beta ∈ right →
      beta₀ < beta ∧ radialTuple nu h beta QhRight QRight) ∧
    radialTuple nu h beta₀ QhLeft QLeft ∧
    radialTuple nu h beta₀ QhRight QRight ∧
    ∃ k : Atom n, QLeft k ≠ QRight k

/-- The fixed-active-policy radial score is the stated cubic with no quadratic
term; its directional tie-break is left-continuous and has the stated switch
jump, and a positive interior chamber maximum has negative cubic curvature. -/
def claim51999 : Prop :=
  ∀ (n : ℕ) (nu : BooleanLaw n) (h : Atom n)
    (I : Set ℝ) (Qh : QueryTree n) (Q : Atom n → QueryTree n),
    isProbabilityLaw nu →
    realInterval I →
    (∀ beta : ℝ, beta ∈ I → radialTuple nu h beta Qh Q) →
      (∀ beta : ℝ, beta ∈ I →
        radialScore (radialLaw h nu beta) h =
          2 * (policyLoss Qh (atomValue h) - queryCost h) +
            beta * radialLinearCoefficient nu h Qh Q +
            beta ^ 3 * radialCubicCoefficient nu h Qh Q) ∧
      (∀ beta₀ : ℝ, beta₀ ∈ I →
        ContinuousWithinAt
          (fun beta => radialScore (radialLaw h nu beta) h)
          (I ∩ Set.Iic beta₀) beta₀) ∧
      (∀ (beta₀ : ℝ) (left right I' : Set ℝ)
        (QhLeft QhRight : QueryTree n)
        (QLeft QRight : Atom n → QueryTree n),
        radialSwitchData nu h beta₀ I' left right
            QhLeft QhRight QLeft QRight →
        (∀ k : Atom n,
          0 ≤ policyProfileDerivativeDrop
            (QLeft k) (QRight k) h nu beta₀) →
          Filter.Tendsto
                (fun beta => radialScore (radialLaw h nu beta) h)
                (nhdsWithin beta₀ (right ∩ Set.Ioi beta₀))
                (nhds
                  (radialScore (radialLaw h nu beta₀) h +
                    beta₀ * ∑ k : Atom n,
                      radialLaw h nu beta₀ k *
                        policyProfileDerivativeDrop
                          (QLeft k) (QRight k) h nu beta₀)) ∧
              0 ≤ beta₀ * ∑ k : Atom n,
                radialLaw h nu beta₀ k *
                  policyProfileDerivativeDrop
                    (QLeft k) (QRight k) h nu beta₀) ∧
      (∀ beta₀ : ℝ,
        positiveInteriorMaximum
          (fun beta => radialScore (radialLaw h nu beta) h) I beta₀ →
          radialCubicCoefficient nu h Qh Q < 0 ∧
            lawAverageLoss nu Q (lawBarycentre nu - atomValue h) >
              policyLoss Qh (lawBarycentre nu - atomValue h))

end
end MathlibPlus.Open.ResearchFormalization.R4031Claim51999
