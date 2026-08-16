import Mathlib

namespace MathlibPlus.Open.Analysis.RankinDoubledCurrentClaim14756

noncomputable section

open scoped BigOperators

/-- The weight-basis index for the coordinate realization of `V_k = Sym^k (ℂ²)`. -/
abbrev WeightIndex (k : ℕ) := Fin (k + 1)

/-- The mixed Rankin-module index `V_k ⊗ V_k`. -/
abbrev MixedIndex (k : ℕ) := WeightIndex k × WeightIndex k

/-- The doubled mixed-module index `(V_k ⊗ V_k)^{⊗ 2}`. -/
abbrev DoubledIndex (k : ℕ) := MixedIndex k × MixedIndex k

/-- The weight `k - 2r` of the basis vector `e_r`. -/
def weightMonomial (k : ℕ) (z : ℂ) (r : WeightIndex k) : ℂ :=
  z ^ ((k : ℤ) - (2 : ℤ) * (r.1 : ℤ))

/-- The diagonal operator `D_k(z)` in the weight basis. -/
def diagonalWeight (k : ℕ) (z : ℂ) :
    Matrix (WeightIndex k) (WeightIndex k) ℂ :=
  fun r s => if r = s then weightMonomial k z r else 0

/-- The basis reversal `e_r ↦ e_(k-r)`. -/
def reverseIndex (k : ℕ) (r : WeightIndex k) : WeightIndex k :=
  ⟨k - r.1, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩

/-- The left (split) reversal `J_k ⊗ I`. -/
def splitReversal (k : ℕ) :
    Matrix (MixedIndex k) (MixedIndex k) ℂ :=
  fun i j =>
    if i.1 = reverseIndex k j.1 ∧ i.2 = j.2 then 1 else 0

/-- The right (compact) reversal `I ⊗ J_k`. -/
def compactReversal (k : ℕ) :
    Matrix (MixedIndex k) (MixedIndex k) ℂ :=
  fun i j =>
    if i.1 = j.1 ∧ i.2 = reverseIndex k j.2 then 1 else 0

/-- The tensor product of two coordinate matrices. -/
def tensorMatrix {ι κ : Type*}
    (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ) :
    Matrix (ι × κ) (ι × κ) ℂ :=
  fun i j => A i.1 j.1 * B i.2 j.2

/-- The mixed operator `T_k(y, α) = D_k(y) ⊗ D_k(α)`. -/
def mixedOperator (k : ℕ) (y α : ℂ) :
    Matrix (MixedIndex k) (MixedIndex k) ℂ :=
  tensorMatrix (diagonalWeight k y) (diagonalWeight k α)

/-- The equal-alignment projector `Q_(k,+)`. -/
def equalAlignment (k : ℕ) :
    Matrix (MixedIndex k) (MixedIndex k) ℂ :=
  fun i j => if i = j ∧ i.1 = i.2 then 1 else 0

/-- The opposite-alignment projector `Q_(k,-)`. -/
def oppositeAlignment (k : ℕ) :
    Matrix (MixedIndex k) (MixedIndex k) ℂ :=
  fun i j => if i = j ∧ i.1.1 + i.2.1 = k then 1 else 0

/-- The parameter-independent doubled current operator. -/
def doubledCurrentOperator (k : ℕ) :
    Matrix (DoubledIndex k) (DoubledIndex k) ℂ :=
  ((4 : ℂ) * Complex.I)⁻¹ •
    (tensorMatrix (equalAlignment k) (equalAlignment k) -
      tensorMatrix (oppositeAlignment k) (oppositeAlignment k))

/-- The split parameter `y = exp(U/2)`. -/
def splitParameter (U : ℝ) : ℂ :=
  (Real.exp (U / 2) : ℂ)

/-- The compact parameter `α = exp(i Φ/2)`. -/
def compactParameter (Φ : ℝ) : ℂ :=
  Complex.exp (Complex.I * ((Φ : ℂ) / 2))

/-- The finite hyperbolic/trigonometric current in the claim. -/
def oddCurrent (k : ℕ) (U Φ : ℝ) : ℂ :=
  ∑ j ∈ Finset.Icc 1 k,
    ∑ m ∈ Finset.Icc 1 j,
      (Real.sinh ((m : ℝ) * U) * Real.sin ((m : ℝ) * Φ) : ℂ)

/-- Apply one coherent reversal to both Rankin copies. -/
def doubledSplitReversal (k : ℕ) :
    Matrix (DoubledIndex k) (DoubledIndex k) ℂ :=
  tensorMatrix (splitReversal k) (splitReversal k)

/-- Apply the other coherent reversal to both Rankin copies. -/
def doubledCompactReversal (k : ℕ) :
    Matrix (DoubledIndex k) (DoubledIndex k) ℂ :=
  tensorMatrix (compactReversal k) (compactReversal k)

/-- Apply the product of split and compact reversals on both copies. -/
def doubledProductReversal (k : ℕ) :
    Matrix (DoubledIndex k) (DoubledIndex k) ℂ :=
  tensorMatrix (splitReversal k * compactReversal k)
    (splitReversal k * compactReversal k)

/--
The doubled mixed-module trace realizes the exact quadratic current.  The
last clause records the essential second copy: for positive degree no fixed
one-copy endomorphism can turn the mixed operator into this quadratic trace
functional for all split and compact parameters.
-/
def claim14756 : Prop :=
  ∀ (k : ℕ) (U Φ : ℝ),
    Matrix.trace
        (tensorMatrix
          (mixedOperator k (splitParameter U) (compactParameter Φ))
          (mixedOperator k (splitParameter U) (compactParameter Φ)) *
          doubledCurrentOperator k) =
      oddCurrent k U Φ ∧
    doubledSplitReversal k * doubledCurrentOperator k * doubledSplitReversal k =
      -doubledCurrentOperator k ∧
    doubledCompactReversal k * doubledCurrentOperator k * doubledCompactReversal k =
      -doubledCurrentOperator k ∧
    doubledProductReversal k * doubledCurrentOperator k * doubledProductReversal k =
      doubledCurrentOperator k ∧
    (0 < k →
      ¬ ∃ L : Matrix (MixedIndex k) (MixedIndex k) ℂ,
        ∀ (U Φ : ℝ),
          Matrix.trace
              (mixedOperator k (splitParameter U) (compactParameter Φ) * L) =
            oddCurrent k U Φ)

end

end MathlibPlus.Open.Analysis.RankinDoubledCurrentClaim14756
