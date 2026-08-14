import Mathlib

open scoped BigOperators

noncomputable section

namespace MathlibPlus.Open.ResearchFormalizationBatch019ffedf

open Filter Set Topology

/-- Finite cluster values are limits along strictly increasing subsequences. -/
def finiteRealClusterSet (u : ℕ → ℝ) : Set ℝ :=
  {x | ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (u ∘ φ) atTop (𝓝 x)}

/-- Convergence on the rows outside the range of a selected sequence. -/
def convergesOffRange (u : ℕ → ℝ) (selected : ℕ → ℕ) (c : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ,
    ∀ k : ℕ, N ≤ k → k ∉ Set.range selected → |u k - c| < ε

/-- Powers of two, as used by the dyadic-row assertion. -/
def isPowerOfTwo (n : ℕ) : Prop := ∃ r : ℕ, n = 2 ^ r

def goodDyadicRow (θ₀ : ℝ) (R n : ℕ) (κ : ℝ) : Prop :=
  isPowerOfTwo n ∧
    |Real.cos ((n : ℝ) * θ₀)| ≥ κ ∧
      ∀ s : ℕ, Odd s → s ≤ R →
        Real.cos (((n * s : ℕ) : ℝ) * θ₀) ≠ 0

/-- Claim 31359: arbitrarily large good dyadic rows. -/
def claim31359 : Prop :=
  ∀ θ₀ : ℝ, θ₀ ∈ Icc 0 Real.pi →
    ∀ R : ℕ, Odd R → 0 < R →
      ∃ κ : ℝ, 0 < κ ∧ ∀ B : ℕ, ∃ n : ℕ,
        B ≤ n ∧ goodDyadicRow θ₀ R n κ

/-- Chebyshev angles and nodes, using zero-based indices. -/
def chebyshevAngle (n : ℕ) (k : Fin n) : ℝ :=
  ((2 * k.1 + 1 : ℕ) : ℝ) * Real.pi / (2 * (n : ℝ))

def chebyshevNode (n : ℕ) (k : Fin n) : ℝ :=
  Real.cos (chebyshevAngle n k)

def chebyshevLagrangeBasis (n : ℕ) (x : ℝ) (k l : Fin n) : ℝ :=
  if l = k then 1 else
    (x - chebyshevNode n l) / (chebyshevNode n k - chebyshevNode n l)

def chebyshevLagrangeValue (f : ℝ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  if h : 0 < n then
    ∑ k : Fin n, f (chebyshevNode n k) *
      ∏ l : Fin n, chebyshevLagrangeBasis n x k l
  else 0

def chebyshevRowValue (f : ℝ → ℝ) (θ₀ : ℝ) (n : ℕ) : ℝ :=
  chebyshevLagrangeValue f n (Real.cos θ₀)

def chebyshevRowSequence (f : ℝ → ℝ) (θ₀ : ℝ) : ℕ → ℝ :=
  chebyshevRowValue f θ₀

def angleRowValue (g : ℝ → ℝ) (θ₀ : ℝ) (n : ℕ) : ℝ :=
  if h : 0 < n then
    ∑ k : Fin n, g (chebyshevAngle n k) *
      ∏ l : Fin n, chebyshevLagrangeBasis n (Real.cos θ₀) k l
  else 0

def angleRowSequence (g : ℝ → ℝ) (θ₀ : ℝ) : ℕ → ℝ :=
  angleRowValue g θ₀

def chebyshevLebesgueValue (n : ℕ) (θ₀ : ℝ) : ℝ :=
  if h : 0 < n then
    ∑ k : Fin n, abs (∏ l : Fin n,
      chebyshevLagrangeBasis n (Real.cos θ₀) k l)
  else 0

def isChebyshevNodeRow (n : ℕ) (θ : ℝ) : Prop :=
  ∃ k : Fin n, θ = chebyshevAngle n k

def explicitLambdaWeight (θ₀ : ℝ) (n : ℕ) (k : Fin n) : ℝ :=
  Real.cos ((n : ℝ) * θ₀) * (-1 : ℝ) ^ k.1 *
    Real.sin (chebyshevAngle n k) /
      ((n : ℝ) * (Real.cos θ₀ - chebyshevNode n k))

def chebyshevFiniteClusterSet (f : ℝ → ℝ) (θ₀ : ℝ) : Set ℝ :=
  finiteRealClusterSet (chebyshevRowSequence f θ₀)

def angleVanishingNear (g : ℝ → ℝ) (θ₀ : ℝ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ θ : ℝ, θ ∈ Icc 0 Real.pi →
    |θ - θ₀| < ε → g θ = 0

def reducedOddDenominatorAngle (θ : ℝ) : Prop :=
  ∃ p q : ℕ, 0 < q ∧ p ≤ q ∧ Nat.Coprime p q ∧ Odd q ∧
    θ / Real.pi = (p : ℝ) / (q : ℝ)

def irrationalReal (x : ℝ) : Prop :=
  ¬ ∃ a b : ℤ, b ≠ 0 ∧ x = (a : ℝ) / (b : ℝ)

/-- Claim 31356: the pointwise cluster set and angle-variable row functional. -/
def claim31356 : Prop :=
  ∀ (f : ℝ → ℝ) (θ₀ : ℝ),
    θ₀ ∈ Icc 0 Real.pi → ContinuousOn f (Icc (-1 : ℝ) 1) →
      chebyshevFiniteClusterSet f θ₀ =
        finiteRealClusterSet (chebyshevRowSequence f θ₀) ∧
      (∀ n : ℕ,
        angleRowValue (fun θ : ℝ => f (Real.cos θ)) θ₀ n =
          chebyshevRowValue f θ₀ n)

/-- Claim 31357: explicit Lagrange weights and the exact node-row branch. -/
def claim31357 : Prop :=
  ∀ (g : ℝ → ℝ) (θ₀ : ℝ) (n : ℕ),
    θ₀ ∈ Icc 0 Real.pi → 0 < n →
      ((¬ isChebyshevNodeRow n θ₀) →
        angleRowValue g θ₀ n =
          ∑ k : Fin n, explicitLambdaWeight θ₀ n k *
            g (chebyshevAngle n k)) ∧
      (isChebyshevNodeRow n θ₀ → angleRowValue g θ₀ n = g θ₀)

/-- Claim 31358: a continuous angle function vanishing near the evaluation
angle has rows converging to zero. -/
def claim31358 : Prop :=
  ∀ (g : ℝ → ℝ) (θ₀ : ℝ),
    θ₀ ∈ Icc 0 Real.pi → ContinuousOn g (Icc 0 Real.pi) →
      angleVanishingNear g θ₀ →
        Tendsto (angleRowSequence g θ₀) atTop (𝓝 0)

/-- Claim 31367: a sequence in a closed set with exactly the prescribed finite
cluster set. -/
def claim31367 : Prop :=
  ∀ A : Set ℝ, A.Nonempty → IsClosed A →
    ∃ a : ℕ → ℝ, (∀ m : ℕ, a m ∈ A) ∧ finiteRealClusterSet a = A

/-- Claim 31369: merging selected rows with the complementary limit. -/
def claim31369 : Prop :=
  ∀ (A : Set ℝ) (c : ℝ) (a u : ℕ → ℝ) (n : ℕ → ℕ),
    c ∈ A → finiteRealClusterSet a = A → StrictMono n →
      (∀ m : ℕ, u (n m) = a m) → convergesOffRange u n c →
        finiteRealClusterSet u = A

/-- Claim 31370: divergence at reduced rational angles with odd denominator. -/
def claim31370 : Prop :=
  ∀ θ₀ : ℝ, θ₀ ∈ Icc 0 Real.pi → reducedOddDenominatorAngle θ₀ →
    ∃ f : ℝ → ℝ,
      ContinuousOn f (Icc (-1 : ℝ) 1) ∧
      Tendsto (fun n : ℕ => |chebyshevRowSequence f θ₀ n|) atTop atTop ∧
      finiteRealClusterSet (chebyshevRowSequence f θ₀) = (∅ : Set ℝ)

/-- Claim 31371: even reduced denominators force infinitely many node rows and
a finite cluster value for every continuous interpoland. -/
def claim31371 : Prop :=
  ∀ (θ₀ : ℝ) (a b s : ℕ),
    θ₀ ∈ Icc 0 Real.pi → 0 < b → Nat.Coprime a b → b = 2 * s →
      θ₀ / Real.pi = (a : ℝ) / (b : ℝ) →
        (∀ m : ℕ, Odd m → isChebyshevNodeRow (s * m) θ₀) ∧
        (∀ f : ℝ → ℝ, ContinuousOn f (Icc (-1 : ℝ) 1) →
          f (Real.cos θ₀) ∈ finiteRealClusterSet (chebyshevRowSequence f θ₀))

/-- Claim 31372: an irrational angle has a near-half-integer subsequence,
nearby nodes, bounded Lebesgue values, and universal convergence. -/
def claim31372 : Prop :=
  ∀ θ₀ : ℝ, θ₀ ∈ Icc 0 Real.pi → irrationalReal (θ₀ / Real.pi) →
    ∃ C : ℝ, 0 < C ∧ ∃ n : ℕ → ℕ,
      StrictMono n ∧
      (∀ j : ℕ, 0 < n j ∧ ∃ z : ℤ,
        |((n j : ℝ) * θ₀ / Real.pi) - ((z : ℝ) + (1 / 2 : ℝ))| ≤
          C / (n j : ℝ)) ∧
      (∃ Ccos : ℝ, 0 ≤ Ccos ∧ ∃ J : ℕ, ∀ j : ℕ, J ≤ j →
        |Real.cos ((n j : ℝ) * θ₀)| ≤ Ccos / (n j : ℝ)) ∧
      (∃ D : ℝ, 0 ≤ D ∧ ∃ J : ℕ, ∀ j : ℕ, J ≤ j →
        ∃ k : Fin (n j),
          |chebyshevAngle (n j) k - θ₀| ≤ D / (n j : ℝ) ^ 2) ∧
      (∃ B : ℝ, ∀ j : ℕ, chebyshevLebesgueValue (n j) θ₀ ≤ B) ∧
      (∀ f : ℝ → ℝ, ContinuousOn f (Icc (-1 : ℝ) 1) →
        Tendsto (fun j : ℕ => chebyshevRowSequence f θ₀ (n j)) atTop
          (𝓝 (f (Real.cos θ₀)))) ∧
      (∀ f : ℝ → ℝ, ContinuousOn f (Icc (-1 : ℝ) 1) →
        finiteRealClusterSet (chebyshevRowSequence f θ₀) ≠ (∅ : Set ℝ))

/-- Claim 31373: the complete nonempty/empty finite-cluster-set classification. -/
def claim31373 : Prop :=
  ∀ θ₀ : ℝ, θ₀ ∈ Icc 0 Real.pi →
    (∀ A : Set ℝ, A.Nonempty → IsClosed A →
      ∃ f : ℝ → ℝ,
        ContinuousOn f (Icc (-1 : ℝ) 1) ∧
        finiteRealClusterSet (chebyshevRowSequence f θ₀) = A) ∧
    ((∃ f : ℝ → ℝ,
        ContinuousOn f (Icc (-1 : ℝ) 1) ∧
        finiteRealClusterSet (chebyshevRowSequence f θ₀) = (∅ : Set ℝ)) ↔
      reducedOddDenominatorAngle θ₀)

/-- Mixed-support degree-p exponent vectors from Claim 31453. -/
def MixedExponent (p m : ℕ) :=
  {ν : Fin m → Fin p //
    (∑ i : Fin m, (ν i : ℕ)) = p ∧
    (∀ i : Fin m, (ν i : ℕ) < p) ∧
    2 ≤ Fintype.card {i : Fin m // 0 < (ν i : ℕ)}}

noncomputable instance mixedExponentFinite (p m : ℕ) : Finite (MixedExponent p m) :=
  Finite.of_injective Subtype.val Subtype.val_injective

noncomputable instance mixedExponentFintype (p m : ℕ) : Fintype (MixedExponent p m) :=
  Fintype.ofFinite _

def mixedSupportCard {p m : ℕ} (ν : MixedExponent p m) : ℕ :=
  Fintype.card {i : Fin m // 0 < (ν.1 i : ℕ)}

def mixedCoefficient {p m : ℕ} (ν : MixedExponent p m) : ZMod p :=
  (Nat.factorial (p - 1) : ZMod p) *
    ∏ i : Fin m, (Nat.factorial (ν.1 i : ℕ) : ZMod p)⁻¹

def outputAsOptionalIndex {m : ℕ} (j : Fin (m + 1)) : Option (Fin m) :=
  if h : j.1 = 0 then none else
    some ⟨j.1 - 1, by omega⟩

def somlaiEntry {p m : ℕ} (ν : MixedExponent p m) (j : Fin (m + 1)) : ZMod p :=
  let c := mixedCoefficient ν
  let k : ℕ := mixedSupportCard ν
  match outputAsOptionalIndex j with
  | none => ((k : ℤ) - 2 : ZMod p) * c
  | some i =>
      if (ν.1 i : ℕ) = 0 then ((1 : ℤ) - k : ZMod p) * c
      else ((2 : ℤ) - k : ZMod p) * c

def somlaiCoefficientMatrix (p m : ℕ) :
    Matrix (Fin (m + 1)) (MixedExponent p m) (ZMod p) :=
  fun j ν => somlaiEntry ν j

/-- Claim 31453: the factorial coefficient in the prime residue field. -/
def claim31453 : Prop :=
  ∀ (p m : ℕ), Nat.Prime p →
    ∀ ν : MixedExponent p m,
      mixedCoefficient ν =
        (Nat.factorial (p - 1) : ZMod p) *
          ∏ i : Fin m, (Nat.factorial (ν.1 i : ℕ) : ZMod p)⁻¹

/-- Claim 31454: the displayed output-0 and output-i entries. -/
def claim31454 : Prop :=
  ∀ (p m : ℕ), Nat.Prime p → ∀ ν : MixedExponent p m,
    somlaiCoefficientMatrix p m 0 ν =
        ((mixedSupportCard ν : ℤ) - 2 : ZMod p) * mixedCoefficient ν ∧
    ∀ i : Fin m,
      somlaiCoefficientMatrix p m (Fin.succ i) ν =
        (if (ν.1 i : ℕ) = 0 then
          ((1 : ℤ) - mixedSupportCard ν : ZMod p) * mixedCoefficient ν
        else
          ((2 : ℤ) - mixedSupportCard ν : ZMod p) * mixedCoefficient ν)

/-- A matrix has full row rank when its row vectors are linearly independent. -/
def hasFullRowRank {ι κ R : Type*} [Semiring R] [AddCommMonoid (κ → R)]
    [Module R (κ → R)] (M : Matrix ι κ R) : Prop :=
  LinearIndependent R (fun i => fun k => M i k)

/-- Claim 31455: the four tested matrices have the displayed full row ranks. -/
def claim31455 : Prop :=
  (Fintype.card (MixedExponent 3 4) = 16 ∧
      hasFullRowRank (somlaiCoefficientMatrix 3 4)) ∧
    (Fintype.card (MixedExponent 5 6) = 246 ∧
      hasFullRowRank (somlaiCoefficientMatrix 5 6)) ∧
    (Fintype.card (MixedExponent 5 5) = 121 ∧
      hasFullRowRank (somlaiCoefficientMatrix 5 5)) ∧
    (Fintype.card (MixedExponent 7 8) = 3424 ∧
      hasFullRowRank (somlaiCoefficientMatrix 7 8))

/-- Claim 31456: the four tested mixed-support monomial counts. -/
def claim31456 : Prop :=
  Fintype.card (MixedExponent 3 4) = 16 ∧
  Fintype.card (MixedExponent 5 6) = 246 ∧
  Fintype.card (MixedExponent 5 5) = 121 ∧
  Fintype.card (MixedExponent 7 8) = 3424

end MathlibPlus.Open.ResearchFormalizationBatch019ffedf
