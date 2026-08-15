import Mathlib

namespace MathlibPlus.Open.FormalizationBatch

noncomputable section

/-! The four-alignment cover and its diagonal quotient. -/

abbrev RelativeGroup := ZMod 2 × ZMod 2

/-- The relative character records the sum of the two flip coordinates. -/
def relativeDifference : RelativeGroup →+ ZMod 2 :=
  { toFun := fun g => g.1 + g.2
    map_zero' := by simp
    map_add' := by
      intro g h
      simp [add_assoc, add_left_comm, add_comm] }

/-- The diagonal subgroup `H = {1, ab}` in additive `ZMod 2` notation. -/
def relativeH : AddSubgroup RelativeGroup :=
  AddSubgroup.comap relativeDifference ⊥

abbrev RelativeQuotient := RelativeGroup ⧸ relativeH

def relativeQuotientMap : RelativeGroup →+ RelativeQuotient :=
  QuotientAddGroup.mk' relativeH

def relativeSplitSign (x : ZMod 2) : ℝ :=
  if x = 0 then 1 else -1

def relativeSplitCharacter (g : RelativeGroup) : ℂ :=
  relativeSplitSign g.1

def relativeCompactCharacter (g : RelativeGroup) : ℂ :=
  relativeSplitSign g.2

def relativeCharacter (i : Fin 4) (g : RelativeGroup) : ℂ :=
  match i.1 with
  | 0 => 1
  | 1 => relativeSplitCharacter g
  | 2 => relativeCompactCharacter g
  | _ => (relativeSplitSign (g.1 + g.2) : ℂ)

def relativeCharacterRel (g : RelativeGroup) : ℂ :=
  (relativeSplitSign (g.1 + g.2) : ℂ)

def relativeMeasure (lambda : ℝ) (g : RelativeGroup) : ℝ :=
  (1 + lambda * relativeSplitSign (g.1 + g.2)) / 4

def relativeFourierMultiplier (lambda : ℝ) (i : Fin 4) : ℂ :=
  ∑ g : RelativeGroup, (relativeMeasure lambda g : ℂ) * relativeCharacter i g

def relativeMultiplierTarget (lambda : ℝ) (i : Fin 4) : ℂ :=
  match i.1 with
  | 0 => 1
  | 1 => 0
  | 2 => 0
  | _ => (lambda : ℂ)

def relativePushforward (f : RelativeGroup → ℝ) (q : RelativeQuotient) : ℝ := by
  classical
  exact ∑ g : RelativeGroup, if relativeQuotientMap g = q then f g else 0

def relativeZeroCoset : RelativeQuotient := relativeQuotientMap 0

def relativeFlipCoset : RelativeQuotient :=
  relativeQuotientMap ((1 : ZMod 2), (0 : ZMod 2))

def relativePushforwardWeights (lambda : ℝ) : Prop :=
  relativeZeroCoset ≠ relativeFlipCoset ∧
    (∀ q : RelativeQuotient,
      q = relativeZeroCoset ∨ q = relativeFlipCoset) ∧
    relativePushforward (relativeMeasure lambda) relativeZeroCoset = (1 + lambda) / 2 ∧
    relativePushforward (relativeMeasure lambda) relativeFlipCoset = (1 - lambda) / 2

def relativeHInvariant (f : RelativeGroup → ℝ) : Prop :=
  ∀ g h, h ∈ relativeH → f (g + h) = f g

def relativeConvolution (f g : RelativeGroup → ℝ) : RelativeGroup → ℝ :=
  fun x => ∑ y : RelativeGroup, f y * g (x - y)

def relativeP (lambda : ℝ) (f : RelativeGroup → ℝ) : RelativeGroup → ℝ :=
  fun x => (1 + lambda) / 2 * f x + (1 - lambda) / 2 *
    f (x + ((1 : ZMod 2), (0 : ZMod 2)))

def relativeNoChannelLoss (lambda : ℝ) : Prop :=
  lambda > 0 →
    ∀ f g : RelativeGroup → ℝ,
      relativeHInvariant f → relativeHInvariant g →
      relativeP lambda f = relativeP lambda g → f = g

/--
Four-way probability measure descends faithfully: the measure has the four
Fourier multipliers `(1,0,0,λ)`, its quotient weights are
`((1+λ)/2,(1-λ)/2)`, and on paired input it is precisely `P_λ` without
losing a surviving channel for `λ > 0`.
-/
def four_way_probability_measure_descends_faithfully_claim7774 : Prop :=
  ∀ lambda : ℝ, 0 ≤ lambda → lambda ≤ 1 →
    (∀ g : RelativeGroup, 0 ≤ relativeMeasure lambda g) ∧
    (∑ g : RelativeGroup, relativeMeasure lambda g = 1) ∧
    (∀ i : Fin 4,
      relativeFourierMultiplier lambda i = relativeMultiplierTarget lambda i) ∧
    relativePushforwardWeights lambda ∧
    (∀ f : RelativeGroup → ℝ,
      relativeHInvariant f →
      relativeConvolution (relativeMeasure lambda) f = relativeP lambda f) ∧
    relativeNoChannelLoss lambda

/-! The polarized mixed-coefficient state map. -/

abbrev PauliSpace := Matrix (Fin 2) (Fin 2) ℂ

/-- A polarized monomial realization of `Sym^k(ℂ²)` with its indexed basis. -/
abbrev PolarizedSymmetricPower (k : ℕ) := Sym (Fin 2) k →₀ ℂ

abbrev MixedCoefficientSpace (k : ℕ) :=
  TensorProduct ℂ (PolarizedSymmetricPower k) (PolarizedSymmetricPower k)

def weightMultiset (k : ℕ) (i : Fin (k + 1)) : Multiset (Fin 2) :=
  Multiset.replicate (k - i.1) 0 + Multiset.replicate i.1 1

def weightMonomial (k : ℕ) (i : Fin (k + 1)) : Sym (Fin 2) k :=
  ⟨weightMultiset k i, by
    have hi : i.1 ≤ k := Nat.le_of_lt_succ i.isLt
    simp [weightMultiset, Nat.sub_add_cancel hi]⟩

def polarizedBasisVector (k : ℕ) (i : Fin (k + 1)) : PolarizedSymmetricPower k :=
  Finsupp.single (weightMonomial k i) 1

def reverseWeightIndex (k : ℕ) (i : Fin (k + 1)) : Fin (k + 1) :=
  ⟨k - i.1, Nat.lt_succ_of_le (Nat.sub_le _ _ )⟩

def weightValue (k : ℕ) (i : Fin (k + 1)) : ℂ :=
  (k : ℂ) - 2 * (i.1 : ℂ)

def diagonalState (k : ℕ) : MixedCoefficientSpace k :=
  ∑ i : Fin (k + 1),
    polarizedBasisVector k i ⊗ₜ[ℂ] polarizedBasisVector k i

def antidiagonalState (k : ℕ) : MixedCoefficientSpace k :=
  ∑ i : Fin (k + 1),
    polarizedBasisVector k (reverseWeightIndex k i) ⊗ₜ[ℂ] polarizedBasisVector k i

def weightedDiagonalState (k : ℕ) : MixedCoefficientSpace k :=
  ∑ i : Fin (k + 1),
    weightValue k i •
      (polarizedBasisVector k i ⊗ₜ[ℂ] polarizedBasisVector k i)

def weightedAntidiagonalState (k : ℕ) : MixedCoefficientSpace k :=
  -∑ i : Fin (k + 1),
    weightValue k i •
      (polarizedBasisVector k (reverseWeightIndex k i) ⊗ₜ[ℂ]
        polarizedBasisVector k i)

def pauliICoefficient (B : PauliSpace) : ℂ :=
  (B 0 0 + B 1 1) / 2

def pauliXCoefficient (B : PauliSpace) : ℂ :=
  (B 0 1 + B 1 0) / 2

def pauliZCoefficient (B : PauliSpace) : ℂ :=
  (B 0 0 - B 1 1) / 2

def pauliIYCoefficient (B : PauliSpace) : ℂ :=
  (B 0 1 - B 1 0) / 2

def stateMap (k : ℕ) : PauliSpace → MixedCoefficientSpace k :=
  fun B =>
    pauliICoefficient B • diagonalState k +
      pauliXCoefficient B • antidiagonalState k +
      pauliZCoefficient B • weightedDiagonalState k +
      pauliIYCoefficient B • weightedAntidiagonalState k

def coefficientFunctional (k : ℕ) (i : Fin (k + 1)) :
    PolarizedSymmetricPower k →ₗ[ℂ] ℂ :=
  Finsupp.lapply (weightMonomial k i)

def mixedCell (k : ℕ) (i j : Fin (k + 1)) :
    MixedCoefficientSpace k →ₗ[ℂ] ℂ :=
  TensorProduct.lift
    ((coefficientFunctional k i).smulRight (coefficientFunctional k j))

def weightSequenceNonconstant (k : ℕ) : Prop :=
  ∃ i j : Fin (k + 1), weightValue k i ≠ weightValue k j

def independentPair {k : ℕ} (u v : MixedCoefficientSpace k) : Prop :=
  ∀ a b : ℂ, a • u + b • v = 0 → a = 0 ∧ b = 0

def endpointSeparation (k : ℕ) : Prop :=
  mixedCell k 0 0 (diagonalState k) ≠ 0 ∧
    mixedCell k 0 0 (antidiagonalState k) = 0 ∧
    mixedCell k 0 ⟨k, Nat.lt_succ_self k⟩ (diagonalState k) = 0 ∧
    mixedCell k 0 ⟨k, Nat.lt_succ_self k⟩ (antidiagonalState k) ≠ 0

/--
For every positive `k`, the state map from the Pauli space to the mixed
coefficient module is injective.  Its diagonal and anti-diagonal pairs are
independent, the weight sequence is nonconstant, and endpoint cells separate
the two supports even when their central cells coincide.
-/
def injectivity_of_state_map_claim7880 : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    Function.Injective (stateMap k) ∧
      weightSequenceNonconstant k ∧
      independentPair (diagonalState k) (weightedDiagonalState k) ∧
      independentPair (antidiagonalState k) (weightedAntidiagonalState k) ∧
      endpointSeparation k

end
end MathlibPlus.Open.FormalizationBatch
