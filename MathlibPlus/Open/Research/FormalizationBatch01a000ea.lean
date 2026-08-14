import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Research

noncomputable section
open scoped Classical

abbrev PosNat := {n : ℕ // 0 < n}

def positiveDivisors (n : PosNat) : Finset ℕ :=
  (Finset.Icc 1 (n : ℕ)).filter (fun d => d ∣ (n : ℕ))

noncomputable def cpower (n : PosNat) (s : ℂ) : ℂ :=
  Complex.exp (s * Complex.log (n : ℂ))

noncomputable def divisorPowerSum (s : ℂ) (n : PosNat) : ℂ :=
  Finset.sum (positiveDivisors n) (fun d => Complex.exp (s * Complex.log (d : ℂ)))

noncomputable def rawDivisorMultiplier (r : ℂ) (n : PosNat) : ℂ :=
  cpower n (-r) * divisorPowerSum (2 * r - 1) n

noncomputable def unitaryDivisorMultiplier (r : ℂ) (n : PosNat) : ℂ :=
  cpower n (1 / 2 - r) * divisorPowerSum (2 * r - 1) n

def divisorCount (n : PosNat) : ℕ := (positiveDivisors n).card

def claim_7029 : Prop :=
  ∀ (r : ℂ) (n : PosNat),
    (unitaryDivisorMultiplier r n =
        (Real.sqrt (n : ℝ) : ℂ) * rawDivisorMultiplier r n /
          rawDivisorMultiplier r ⟨1, by decide⟩) ∧
    rawDivisorMultiplier (1 / 2) n =
      cpower n (-1 / 2) * (divisorCount n : ℂ)

def divisorIndex (n : PosNat) := {d : ℕ // d ∈ positiveDivisors n}

noncomputable def divisorComplement (n : PosNat) (d : divisorIndex n) : divisorIndex n :=
  ⟨(n : ℕ) / d.1, by
    have hd := (Finset.mem_filter.mp d.2).2
    have hdpos : 0 < d.1 := by
      exact (Finset.mem_Icc.mp (Finset.mem_filter.mp d.2).1).1
    have hndvd : d.1 ∣ (n : ℕ) := hd
    have hnpos : 0 < (n : ℕ) := n.2
    have hquotpos : 0 < (n : ℕ) / d.1 :=
      Nat.div_pos (Nat.le_of_dvd hnpos hndvd) hdpos
    have hquotle : (n : ℕ) / d.1 ≤ (n : ℕ) := Nat.div_le_self _ _
    have hquotdvd : (n : ℕ) / d.1 ∣ (n : ℕ) := by
      refine ⟨d.1, ?_⟩
      exact (Nat.div_mul_cancel hndvd).symm
    exact Finset.mem_filter.mpr ⟨
      Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hquotpos), hquotle⟩,
      hquotdvd⟩⟩

abbrev DivisorSpace (n : PosNat) := divisorIndex n → ℂ

noncomputable def divisorBasis (n : PosNat) (d : divisorIndex n) : DivisorSpace n :=
  fun q => if q = d then 1 else 0

noncomputable def diagonalWeight (n : PosNat) (d : divisorIndex n) : ℝ :=
  Real.rpow (((d.1 : ℝ) ^ 2) / (n : ℝ)) (11 / 2)

noncomputable def positiveDiagonal (n : PosNat) (v : DivisorSpace n) : DivisorSpace n :=
  fun d => (diagonalWeight n d : ℂ) * v d

noncomputable def divisorInvolution (n : PosNat) (v : DivisorSpace n) : DivisorSpace n :=
  fun d => v (divisorComplement n d)

def claim_7020 : Prop :=
  ∀ (n : PosNat) (d : divisorIndex n),
    positiveDiagonal n (divisorBasis n d) =
        (diagonalWeight n d : ℂ) • divisorBasis n d ∧
    divisorInvolution n (divisorBasis n d) =
        divisorBasis n (divisorComplement n d) ∧
    0 ≤ diagonalWeight n d ∧
    ∀ v : DivisorSpace n, divisorInvolution n (divisorInvolution n v) = v

noncomputable def complexPowerOfReal (b : ℝ) (s : ℂ) : ℂ :=
  Complex.exp (s * Complex.log (b : ℂ))

noncomputable def degreeTwoNormalizer (r : ℂ) : ℂ :=
  Complex.Gamma r * Complex.Gamma (r + 6) * Complex.Gamma (r + 11 / 2) *
    complexPowerOfReal 2 (2 * r - 2) *
    complexPowerOfReal Real.pi (-r - 1 / 2) *
    riemannZeta (2 * r) * riemannZeta (4 * r - 2)

def claim_7033 : Prop :=
  Filter.Tendsto
    (fun r : ℂ => (r - (1 / 2 : ℂ)) * degreeTwoNormalizer r)
    (nhdsWithin (1 / 2 : ℂ) {z : ℂ | z ≠ (1 / 2 : ℂ)})
    (nhds ((-155925 / 64 : ℚ) : ℂ))

abbrev SymmetricPowerCoordinate (k : ℕ) := Fin (k + 1) → ℂ
abbrev TensorCoordinate (k : ℕ) := (Fin (k + 1) × Fin (k + 1)) → ℂ

def tensorBasis (k : ℕ) (p : Fin (k + 1) × Fin (k + 1)) : TensorCoordinate k :=
  fun q => if q = p then 1 else 0

noncomputable def equalAlignmentProjector (k : ℕ) :
    TensorCoordinate k →ₗ[ℂ] TensorCoordinate k :=
  { toFun := fun x p => if p.1.1 = p.2.1 then x p else 0
    map_add' := by
      intro x y
      ext p
      by_cases h : p.1.1 = p.2.1 <;> simp [h]
    map_smul' := by
      intro c x
      ext p
      by_cases h : p.1.1 = p.2.1 <;> simp [h] }

noncomputable def oppositeAlignmentProjector (k : ℕ) :
    TensorCoordinate k →ₗ[ℂ] TensorCoordinate k :=
  { toFun := fun x p => if p.1.1 + p.2.1 = k then x p else 0
    map_add' := by
      intro x y
      ext p
      by_cases h : p.1.1 + p.2.1 = k <;> simp [h]
    map_smul' := by
      intro c x
      ext p
      by_cases h : p.1.1 + p.2.1 = k <;> simp [h] }

noncomputable def coordinateInner (k : ℕ) (x y : TensorCoordinate k) : ℂ :=
  Finset.sum Finset.univ (fun p => star (x p) * y p)

noncomputable def coordinateTrace (k : ℕ)
    (A : TensorCoordinate k →ₗ[ℂ] TensorCoordinate k) : ℂ :=
  Finset.sum Finset.univ (fun p => A (tensorBasis k p) p)

def reversedIndex (k : ℕ) (r : Fin (k + 1)) : Fin (k + 1) :=
  ⟨k - r.1, by omega⟩

noncomputable def leftReversal (k : ℕ) :
    TensorCoordinate k →ₗ[ℂ] TensorCoordinate k :=
  { toFun := fun x p => x (reversedIndex k p.1, p.2)
    map_add' := by
      intro x y
      ext p
      simp
    map_smul' := by
      intro c x
      ext p
      simp }

noncomputable def rightReversal (k : ℕ) :
    TensorCoordinate k →ₗ[ℂ] TensorCoordinate k :=
  { toFun := fun x p => x (p.1, reversedIndex k p.2)
    map_add' := by
      intro x y
      ext p
      simp
    map_smul' := by
      intro c x
      ext p
      simp }

noncomputable def simultaneousReversal (k : ℕ) :
    TensorCoordinate k →ₗ[ℂ] TensorCoordinate k :=
  { toFun := fun x p => x (reversedIndex k p.1, reversedIndex k p.2)
    map_add' := by
      intro x y
      ext p
      simp
    map_smul' := by
      intro c x
      ext p
      simp }

def claim_7064 : Prop :=
  ∀ k : ℕ,
    (∀ x : TensorCoordinate k,
      equalAlignmentProjector k (equalAlignmentProjector k x) =
        equalAlignmentProjector k x) ∧
    (∀ x : TensorCoordinate k,
      oppositeAlignmentProjector k (oppositeAlignmentProjector k x) =
        oppositeAlignmentProjector k x) ∧
    (∀ x y : TensorCoordinate k,
      coordinateInner k (equalAlignmentProjector k x) y =
        coordinateInner k x (equalAlignmentProjector k y)) ∧
    (∀ x y : TensorCoordinate k,
      coordinateInner k (oppositeAlignmentProjector k x) y =
        coordinateInner k x (oppositeAlignmentProjector k y)) ∧
    LinearMap.range (equalAlignmentProjector k) =
      Submodule.span ℂ (Set.range (fun r : Fin (k + 1) =>
        tensorBasis k (r, r))) ∧
    LinearMap.range (oppositeAlignmentProjector k) =
      Submodule.span ℂ (Set.range (fun r : Fin (k + 1) =>
        tensorBasis k (r, reversedIndex k r))) ∧
    Module.finrank ℂ (LinearMap.range (equalAlignmentProjector k)) = k + 1 ∧
    Module.finrank ℂ (LinearMap.range (oppositeAlignmentProjector k)) = k + 1 ∧
    coordinateTrace k (equalAlignmentProjector k) = (k + 1 : ℕ) ∧
    coordinateTrace k (oppositeAlignmentProjector k) = (k + 1 : ℕ) ∧
    (0 < k → equalAlignmentProjector k ≠ oppositeAlignmentProjector k) ∧
    (Even k →
      LinearMap.range (equalAlignmentProjector k) ⊓
          LinearMap.range (oppositeAlignmentProjector k) =
        Submodule.span ℂ (Set.singleton
          (tensorBasis k
            (⟨k / 2, by omega⟩, ⟨k / 2, by omega⟩)))) ∧
    (∀ x : TensorCoordinate k,
      leftReversal k (equalAlignmentProjector k (leftReversal k x)) =
        oppositeAlignmentProjector k x) ∧
    (∀ x : TensorCoordinate k,
      rightReversal k (equalAlignmentProjector k (rightReversal k x)) =
        oppositeAlignmentProjector k x) ∧
    (∀ x : TensorCoordinate k,
      simultaneousReversal k (equalAlignmentProjector k (simultaneousReversal k x)) =
        equalAlignmentProjector k x) ∧
    (∀ x : TensorCoordinate k,
      simultaneousReversal k (oppositeAlignmentProjector k (simultaneousReversal k x)) =
        oppositeAlignmentProjector k x)

noncomputable def character (k : ℕ) (z : ℂ) : ℂ :=
  Finset.sum Finset.univ (fun r : Fin (k + 1) =>
    z ^ ((k : ℤ) - 2 * (r.1 : ℤ)))


def claim_7067 : Prop :=
  ∀ (k : ℕ) (U Phi : ℝ),
    (character k
        (Complex.exp ((U : ℂ) / 2) * Complex.exp (Complex.I * (Phi : ℂ) / 2)) ^ 2 -
      character k
        (Complex.exp ((U : ℂ) / 2) * Complex.exp (-Complex.I * (Phi : ℂ) / 2)) ^ 2) /
        (4 * Complex.I) =
      (Finset.sum (Finset.Icc 1 k) (fun j =>
        Finset.sum (Finset.Icc 1 j) (fun m =>
          (Real.sinh (m * U) * Real.sin (m * Phi) : ℂ)))) ∧
    (character 1
        (Complex.exp ((U : ℂ) / 2) * Complex.exp (Complex.I * (Phi : ℂ) / 2)) ^ 2 -
      character 1
        (Complex.exp ((U : ℂ) / 2) * Complex.exp (-Complex.I * (Phi : ℂ) / 2)) ^ 2) /
        (4 * Complex.I) =
      (Real.sinh U * Real.sin Phi : ℂ)

end
end MathlibPlus.Open.Research
