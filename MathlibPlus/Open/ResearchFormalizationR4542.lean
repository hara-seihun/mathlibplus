import Mathlib

noncomputable section

namespace MathlibPlus.Open.R4542

/-- Integer partitions retain repeated parts as a multiset of positive integers. -/
structure Partition where
  parts : Multiset ℕ
  positive : ∀ n ∈ parts, 0 < n

abbrev SourceVariable := Option ℕ
abbrev SourceExponent := SourceVariable →₀ ℕ
abbrev TargetExponent := ℕ →₀ ℕ
abbrev SourcePolynomial := MvPolynomial SourceVariable ℤ
abbrev TargetPolynomial := MvPolynomial ℕ ℤ

/-- The source marker is the `none` variable; ordinary variables are `some n`. -/
def z : SourcePolynomial := MvPolynomial.X none

def x (n : ℕ) : SourcePolynomial := MvPolynomial.X (some n)

def partitionWeight (part : Partition) : ℕ := part.parts.sum

def partitionExponent (part : Partition) : SourceExponent :=
  (part.parts.map (fun n : ℕ =>
    (Finsupp.single (some n) 1 : SourceExponent))).sum

def targetPartitionExponent (part : Partition) : TargetExponent :=
  (part.parts.map (fun n : ℕ =>
    (Finsupp.single n 1 : TargetExponent))).sum

def sourceExponent (r : ℕ) (part : Partition) : SourceExponent :=
  Finsupp.single none r + partitionExponent part

def sourceMonomial (r : ℕ) (part : Partition) : SourcePolynomial :=
  MvPolynomial.monomial (sourceExponent r part) 1

def targetMonomial (n : ℕ) (part : Partition) : TargetPolynomial :=
  MvPolynomial.monomial
    (Finsupp.single n 1 + targetPartitionExponent part) 1

def residualWeightExponent (e : SourceExponent) : ℕ :=
  e.sum (fun v n =>
    match v with
    | none => n
    | some k => n * k)
def sourceMonomialWeight (r : ℕ) (part : Partition) : ℕ :=
  residualWeightExponent (sourceExponent r part)

/-- The residual weight assigned to `z^r x_part`. -/
def ResidualWeightSpec : Prop :=
  ∀ (r : ℕ) (part : Partition),
    sourceMonomialWeight r part = r + partitionWeight part

def xMonomial (part : Partition) : SourcePolynomial :=
  MvPolynomial.monomial (partitionExponent part) 1

def shiftExponent (s : ℕ) (e : SourceExponent) : TargetExponent :=
  Finsupp.single (e none + s) 1 +
    e.sum (fun v n =>
      match v with
      | none => 0
      | some k => Finsupp.single k n)

def phiOnCoefficients (s : ℕ) :
    (SourceExponent →₀ ℤ) →ₗ[ℤ] (TargetExponent →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ (shiftExponent s)

/-- The linear marker shift on the coefficient-bearing source algebra. -/
def Phi (s : ℕ) : SourcePolynomial →ₗ[ℤ] TargetPolynomial :=
  { toFun := fun p =>
      AddMonoidAlgebra.ofCoeff
        (phiOnCoefficients s (AddMonoidAlgebra.coeff p))
    map_add' := by
      intro p q
      apply AddMonoidAlgebra.ext
      change
        phiOnCoefficients s
            (AddMonoidAlgebra.coeff p + AddMonoidAlgebra.coeff q) =
          phiOnCoefficients s (AddMonoidAlgebra.coeff p) +
            phiOnCoefficients s (AddMonoidAlgebra.coeff q)
      exact (phiOnCoefficients s).map_add _ _
    map_smul' := by
      intro c p
      apply AddMonoidAlgebra.ext
      change
        phiOnCoefficients s (c • AddMonoidAlgebra.coeff p) =
          c • phiOnCoefficients s (AddMonoidAlgebra.coeff p)
      exact (phiOnCoefficients s).map_smul c (AddMonoidAlgebra.coeff p) }

def ScalarMarkerShiftSpec : Prop :=
  ∀ (s r : ℕ) (part : Partition),
    1 ≤ s →
      Phi s (sourceMonomial r part) = targetMonomial (r + s) part

def D (t : ℕ) : SourcePolynomial :=
    z * x t * x (t + 3)
  - z ^ 2 * x t * x (t + 2)
  - x (t + 1) * x (t + 3)
  + z ^ 2 * x (t + 1) ^ 2
  + x (t + 2) ^ 2
  - z * x (t + 1) * x (t + 2)

def dExp₁ (t : ℕ) : SourceExponent :=
  Finsupp.single none 1 +
    Finsupp.single (some t) 1 +
    Finsupp.single (some (t + 3)) 1

def dExp₂ (t : ℕ) : SourceExponent :=
  Finsupp.single none 2 +
    Finsupp.single (some t) 1 +
    Finsupp.single (some (t + 2)) 1

def dExp₃ (t : ℕ) : SourceExponent :=
  Finsupp.single (some (t + 1)) 1 +
    Finsupp.single (some (t + 3)) 1

def dExp₄ (t : ℕ) : SourceExponent :=
  Finsupp.single none 2 +
    Finsupp.single (some (t + 1)) 2

def dExp₅ (t : ℕ) : SourceExponent :=
  Finsupp.single (some (t + 2)) 2

def dExp₆ (t : ℕ) : SourceExponent :=
  Finsupp.single none 1 +
    Finsupp.single (some (t + 1)) 1 +
    Finsupp.single (some (t + 2)) 1

def dTerms (t : ℕ) : Finset SourceExponent :=
  {dExp₁ t, dExp₂ t, dExp₃ t, dExp₄ t, dExp₅ t, dExp₆ t}

/-- Every term of `D_t` has its displayed residual weight. -/
def DWeight : Prop :=
  ∀ t, 1 ≤ t →
    ∀ e ∈ (D t).support, residualWeightExponent e = 2 * t + 4

/-- The six displayed monomials are exactly the six nonzero supported terms. -/
def DHasSixDistinctTerms : Prop :=
  ∀ t, 1 ≤ t →
    (D t).support = dTerms t ∧
      (dTerms t).card = 6 ∧
      ∀ e ∈ dTerms t, (D t).coeff e ≠ 0

def AdjacentMarkerCommonKernel : Prop :=
  ∀ t : ℕ, 1 ≤ t →
    D t ≠ 0 ∧
      Phi t (D t) = 0 ∧
      Phi (t + 1) (D t) = 0

def DOneCommonKernel : Prop :=
  DHasSixDistinctTerms ∧
    D 1 ≠ 0 ∧
    (∀ e ∈ (D 1).support, residualWeightExponent e = 6) ∧
    Phi 1 (D 1) = 0 ∧
    Phi 2 (D 1) = 0

def zFreeMonomial (part : Partition) : SourcePolynomial := xMonomial part

def SpectatorKernelStability : Prop :=
  ∀ t, 1 ≤ t → ∀ part : Partition,
    Phi t (zFreeMonomial part * D t) = 0 ∧
      Phi (t + 1) (zFreeMonomial part * D t) = 0 ∧
      ∀ e ∈ (zFreeMonomial part * D t).support,
        residualWeightExponent e = 2 * t + 4 + partitionWeight part

end MathlibPlus.Open.R4542
