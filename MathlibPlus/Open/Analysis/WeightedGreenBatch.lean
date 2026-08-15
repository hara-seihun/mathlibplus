import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Analysis

noncomputable section

/-- The concrete Jacobi matrix determined by its diagonal and positive off-diagonal
entries.  The index of `β` is the larger endpoint of an off-diagonal entry. -/
def weightedGreenJacobiMatrix (n : ℕ) (α β : ℕ → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j =>
    if i = j then α i
    else if i.val + 1 = j.val then β j
    else if j.val + 1 = i.val then β i
    else 0

/-- `J ≻ 0` together with positivity of every off-diagonal coefficient that
actually occurs in the finite Jacobi matrix. -/
def positiveWeightedGreenJacobi (n : ℕ) (α β : ℕ → ℝ) : Prop :=
  (∀ k : ℕ, 1 ≤ k → k < n → 0 < β k) ∧
    ∀ x : Fin n → ℝ, x ≠ 0 →
      0 < ∑ i : Fin n, x i *
        (Matrix.mulVec (weightedGreenJacobiMatrix n α β) x) i

/-- The determinant of the leading `k` by `k` principal submatrix.  The
zero value outside the finite range only totalizes the notation; all uses in
these claims have `k ≤ n`. -/
def weightedGreenLeadingDet (n : ℕ) (α β : ℕ → ℝ) (k : ℕ) : ℝ :=
  if h : k ≤ n then
    Matrix.det (fun i j : Fin k =>
      weightedGreenJacobiMatrix n α β
        ⟨i.val, Nat.lt_of_lt_of_le i.isLt h⟩
        ⟨j.val, Nat.lt_of_lt_of_le j.isLt h⟩)
  else 0

/-- The pivot `q_k = D_{k+1}/D_k`. -/
def weightedGreenPivot (n : ℕ) (α β : ℕ → ℝ) (k : ℕ) : ℝ :=
  weightedGreenLeadingDet n α β (k + 1) /
    weightedGreenLeadingDet n α β k

/-- The resistance-gauge normalized continuant solution. -/
def weightedGreenY (n : ℕ) (α β : ℕ → ℝ) (a k : ℕ) : ℝ :=
  weightedGreenLeadingDet n α β k /
    (weightedGreenLeadingDet n α β (a - 1) *
      Finset.prod (Finset.Icc a k) β)

/-- The source `S_k`. -/
def weightedGreenSource (α β : ℕ → ℝ) (k : ℕ) : ℝ :=
  α k - β k - β (k + 1)

/-- The flux `G_k`. -/
def weightedGreenFlux (β Y : ℕ → ℝ) (k : ℕ) : ℝ :=
  β (k + 1) * (Y (k + 1) - Y k)

/-- The resistance coordinate, with `T_{a-1}=0`. -/
def weightedGreenResistance (a : ℕ) (β : ℕ → ℝ) (k : ℕ) : ℝ :=
  if a ≤ k then Finset.sum (Finset.Icc a k) (fun p => (β p)⁻¹) else 0

/-- Weighted-divergence Green equation for the normalized positive solution. -/
def weightedDivergenceGreenEquation : Prop :=
  ∀ (n : ℕ) (α β : ℕ → ℝ) (a b : ℕ),
    positiveWeightedGreenJacobi n α β →
    1 ≤ a → a ≤ b → b ≤ n - 2 →
    ∀ k : ℕ, a ≤ k → k ≤ b →
      β (k + 1) *
          (weightedGreenY n α β a (k + 1) - weightedGreenY n α β a k) -
        β k *
          (weightedGreenY n α β a k - weightedGreenY n α β a (k - 1)) =
      weightedGreenSource α β k * weightedGreenY n α β a k

/-- Twice-summed Green representation in the resistance coordinate. -/
def twiceSummedGreenRepresentation : Prop :=
  ∀ (n : ℕ) (α β : ℕ → ℝ) (a b : ℕ),
    positiveWeightedGreenJacobi n α β →
    1 ≤ a → a ≤ b → b ≤ n - 2 →
    ∀ k : ℕ, a ≤ k → k ≤ b + 1 →
      weightedGreenY n α β a k =
        1 +
            weightedGreenFlux β (weightedGreenY n α β a) (a - 1) *
              weightedGreenResistance a β k +
          Finset.sum (Finset.Icc a (k - 1)) (fun l =>
            weightedGreenSource α β l * weightedGreenY n α β a l *
              (weightedGreenResistance a β k -
                weightedGreenResistance a β l))

/-- Exact projective imbalance formula. -/
def exactProjectiveImbalanceFormula : Prop :=
  ∀ (n : ℕ) (α β : ℕ → ℝ) (a b : ℕ),
    positiveWeightedGreenJacobi n α β →
    1 ≤ a → a ≤ b → b ≤ n - 2 →
    ∀ k : ℕ, a ≤ k → k ≤ b →
      weightedGreenPivot n α β k / β (k + 1) - 1 =
        (weightedGreenFlux β (weightedGreenY n α β a) (a - 1) +
            Finset.sum (Finset.Icc a k) (fun l =>
              weightedGreenSource α β l * weightedGreenY n α β a l)) /
          (β (k + 1) * weightedGreenY n α β a k)

/-- On a source-free block, flux is constant and the normalized solution is
affine in resistance. -/
def sourceFreeBlockIsAffineInResistance : Prop :=
  ∀ (n : ℕ) (α β : ℕ → ℝ) (a b : ℕ),
    positiveWeightedGreenJacobi n α β →
    1 ≤ a → a ≤ b → b ≤ n - 2 →
    (∀ l : ℕ, a ≤ l → l ≤ b → weightedGreenSource α β l = 0) →
    (∀ k : ℕ, a ≤ k → k ≤ b →
      weightedGreenFlux β (weightedGreenY n α β a) k =
        weightedGreenFlux β (weightedGreenY n α β a) (a - 1)) ∧
    (∀ k : ℕ, a ≤ k → k ≤ b + 1 →
      weightedGreenY n α β a k =
        1 + weightedGreenFlux β (weightedGreenY n α β a) (a - 1) *
          weightedGreenResistance a β k)

end

end MathlibPlus.Open.Analysis
