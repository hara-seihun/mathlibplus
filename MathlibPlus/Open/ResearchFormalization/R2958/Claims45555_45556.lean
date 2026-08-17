import Mathlib
import MathlibPlus.Open.ResearchFormalizationR4542

namespace MathlibPlus.Open.ResearchFormalization.R2958

open MathlibPlus.Open.R4542
open scoped BigOperators

noncomputable section

abbrev MarkerPolynomial := MathlibPlus.Open.R4542.SourcePolynomial
abbrev TargetPolynomial := MathlibPlus.Open.R4542.TargetPolynomial

/-- The exponent of the ordinary variables in a multiset monomial. -/
def markerPartExponent (parts : Multiset ℕ) : SourceExponent :=
  (parts.map (fun n : ℕ =>
    (Finsupp.single (some n) 1 : SourceExponent))).sum

def targetPartExponent (parts : Multiset ℕ) : TargetExponent :=
  (parts.map (fun n : ℕ =>
    (Finsupp.single n 1 : TargetExponent))).sum

def markerMonomial (r : ℕ) (parts : Multiset ℕ) : MarkerPolynomial :=
  MvPolynomial.monomial
    (Finsupp.single none r + markerPartExponent parts) 1

def targetMonomialParts (parts : Multiset ℕ) : TargetPolynomial :=
  MvPolynomial.monomial (targetPartExponent parts) 1

def positiveParts (parts : Multiset ℕ) : Prop :=
  ∀ n ∈ parts, 0 < n

def homogeneousMonomialSet (W : ℕ) : Set MarkerPolynomial :=
  {p |
    ∃ r : ℕ, ∃ parts : Multiset ℕ,
      positiveParts parts ∧
        r + parts.sum = W ∧ p = markerMonomial r parts}

def homogeneousDomain (W : ℕ) : Submodule ℤ MarkerPolynomial :=
  Submodule.span ℤ (homogeneousMonomialSet W)

def homogeneousPolynomial (W : ℕ) (p : MarkerPolynomial) : Prop :=
  ∀ e ∈ p.support, residualWeightExponent e = W

def fibreValues {n : ℕ} (nu : Nat.Partition n) : Finset ℕ :=
  nu.parts.toFinset.filter (fun a => 2 ≤ a)

def fibreMonomial {n : ℕ} (nu : Nat.Partition n) (a : ℕ) : MarkerPolynomial :=
  MvPolynomial.monomial
    (Finsupp.single none (a - 2) + markerPartExponent (nu.parts.erase a)) 1

def fibreSpan (W : ℕ) (nu : Nat.Partition (W + 2)) :
    Submodule ℤ MarkerPolynomial :=
  Submodule.span ℤ
    {p | ∃ a ∈ fibreValues nu, p = fibreMonomial nu a}

def augmentationCombination {n : ℕ} (nu : Nat.Partition n)
    (p : MarkerPolynomial) : Prop :=
  ∃ c : ℕ → ℤ,
    p = Finset.sum (fibreValues nu)
      (fun a => c a • fibreMonomial nu a) ∧
      Finset.sum (fibreValues nu) c = 0

def augmentationFibreSpan {n : ℕ} (nu : Nat.Partition n) :
    Submodule ℤ MarkerPolynomial :=
  Submodule.span ℤ {p | augmentationCombination nu p}

def internalDirectSum {V : Type*} [AddCommGroup V]
    (W : Submodule ℤ V) {ι : Type*} [Fintype ι]
    (U : ι → Submodule ℤ V) : Prop :=
  (∀ i, U i ≤ W) ∧
    ∀ v : V, v ∈ W ↔
      ∃! c : ∀ i, U i, (∑ i, (c i : V)) = v

def kernelHomogeneousDomain (W : ℕ) : Submodule ℤ MarkerPolynomial :=
  LinearMap.ker (Phi 2) ⊓ homogeneousDomain W

def elementaryExchange {n : ℕ} (nu : Nat.Partition n) (a b : ℕ) :
    MarkerPolynomial :=
  fibreMonomial nu a - fibreMonomial nu b

def exchangeTargetLeft {n : ℕ} (nu : Nat.Partition n) (a b : ℕ) :
    TargetPolynomial :=
  targetMonomialParts
    ((a - 1) ::ₘ b ::ₘ (nu.parts.erase a).erase b)

def exchangeTargetRight {n : ℕ} (nu : Nat.Partition n) (a b : ℕ) :
    TargetPolynomial :=
  targetMonomialParts
    ((b - 1) ::ₘ a ::ₘ (nu.parts.erase a).erase b)

/-- The displayed six-term simultaneous marker cycle. -/
def markerD6 : MarkerPolynomial :=
  z * x 1 * x 4 - z ^ 2 * x 1 * x 3 - x 2 * x 4 +
    z ^ 2 * x 2 ^ 2 + x 3 ^ 2 - z * x 2 * x 3

def markerD6PhiOneCancellation : TargetPolynomial :=
  MvPolynomial.X 1 * MvPolynomial.X 2 * MvPolynomial.X 4 -
    MvPolynomial.X 1 * (MvPolynomial.X 3) ^ 2 -
    MvPolynomial.X 1 * MvPolynomial.X 2 * MvPolynomial.X 4 +
    (MvPolynomial.X 2) ^ 2 * MvPolynomial.X 3 +
    MvPolynomial.X 1 * (MvPolynomial.X 3) ^ 2 -
    (MvPolynomial.X 2) ^ 2 * MvPolynomial.X 3

def crossFibreExchangeCancellation : Prop :=
  ∃ (nu₁ nu₂ nu₃ : Nat.Partition 8),
    nu₁.parts = {1, 3, 4} ∧
      nu₂.parts = {2, 2, 4} ∧
      nu₃.parts = {2, 3, 3} ∧
      nu₁ ≠ nu₂ ∧ nu₂ ≠ nu₃ ∧ nu₁ ≠ nu₃ ∧
      3 ∈ fibreValues nu₁ ∧ 4 ∈ fibreValues nu₁ ∧
      2 ∈ fibreValues nu₂ ∧ 4 ∈ fibreValues nu₂ ∧
      2 ∈ fibreValues nu₃ ∧ 3 ∈ fibreValues nu₃ ∧
      markerD6 = elementaryExchange nu₁ 3 4 -
          elementaryExchange nu₂ 2 4 + elementaryExchange nu₃ 2 3 ∧
      Phi 1 (elementaryExchange nu₁ 3 4 -
          elementaryExchange nu₂ 2 4 + elementaryExchange nu₃ 2 3) = 0 ∧
      Phi 2 (elementaryExchange nu₁ 3 4 -
          elementaryExchange nu₂ 2 4 + elementaryExchange nu₃ 2 3) = 0

/-- R-2958.2: the homogeneous marker domain and its Phi_2 kernel are
    internal direct sums of the finite output-partition fibres, with the
    stated monomial fibres and one-step exchange trace. -/
def directSumFibreNormalForm_claim45555 : Prop :=
  (∀ W : ℕ,
    internalDirectSum (homogeneousDomain W)
      (fun nu : Nat.Partition (W + 2) => fibreSpan W nu)) ∧
    (∀ W : ℕ,
      internalDirectSum (kernelHomogeneousDomain W)
        (fun nu : Nat.Partition (W + 2) => augmentationFibreSpan nu)) ∧
    (∀ (W : ℕ) (nu : Nat.Partition (W + 2))
      (p : MarkerPolynomial),
      p ∈ homogeneousMonomialSet W →
        (Phi 2 p = targetMonomialParts nu.parts ↔
          ∃ a ∈ fibreValues nu, p = fibreMonomial nu a) ∧
      (∀ a ∈ fibreValues nu,
        Phi 2 (fibreMonomial nu a) = targetMonomialParts nu.parts) ∧
      (∀ a b, a ∈ fibreValues nu → b ∈ fibreValues nu → a ≠ b →
        Phi 1 (elementaryExchange nu a b) =
            exchangeTargetLeft nu a b - exchangeTargetRight nu a b ∧
          exchangeTargetLeft nu a b ≠ 0 ∧
          exchangeTargetRight nu a b ≠ 0 ∧
          exchangeTargetLeft nu a b ≠ exchangeTargetRight nu a b)) ∧
    crossFibreExchangeCancellation

/-- R-2958.3: the explicit first nonzero simultaneous marker cycle, its
    minimal homogeneous weight, its displayed Phi_1 cancellation, and the
    visibility of every individual elementary exchange. -/
def firstSimultaneousMarkerCycle_claim45556 : Prop :=
  markerD6 ≠ 0 ∧
    homogeneousPolynomial 6 markerD6 ∧
    markerD6 ∈ homogeneousDomain 6 ∧
    (∀ W : ℕ, W < 6 →
      ∀ p : MarkerPolynomial, p ∈ homogeneousDomain W →
        Phi 1 p = 0 → Phi 2 p = 0 → p = 0) ∧
    Phi 2 markerD6 = 0 ∧
    Phi 1 markerD6 = 0 ∧
    Phi 1 markerD6 = markerD6PhiOneCancellation ∧
    markerD6PhiOneCancellation = 0 ∧
    (∀ (W : ℕ) (nu : Nat.Partition (W + 2)) (a b : ℕ),
      a ∈ fibreValues nu → b ∈ fibreValues nu → a ≠ b →
        Phi 1 (elementaryExchange nu a b) ≠ 0 ∧
          exchangeTargetLeft nu a b ≠ 0 ∧
          exchangeTargetRight nu a b ≠ 0 ∧
          exchangeTargetLeft nu a b ≠ exchangeTargetRight nu a b) ∧
    crossFibreExchangeCancellation

end

end MathlibPlus.Open.ResearchFormalization.R2958
