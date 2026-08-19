import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R3664

noncomputable section

abbrev A := MvPolynomial ℕ ℤ
abbrev Aℚ := MvPolynomial ℕ ℚ

/-- The variable `x (j + 1)` is represented by `X j`; the index is countable. -/
def xVar (j : ℕ) : A := MvPolynomial.X j

def partVar (a : ℕ) : A := xVar (a - 1)

def weightedDegree (m : ℕ →₀ ℕ) : ℕ :=
  m.sum (fun j e => (j + 1) * e)

def weightedHomogeneous (k : ℕ) (p : A) : Prop :=
  ∀ m ∈ p.support, weightedDegree m = k

/-- `A_k`, with the source's countably many variables and its weight grading. -/
def weightedPart (k : ℕ) : Set A := {p | weightedHomogeneous k p}

/-- The ambient carrier of `⊕_{a=1}^n A_(n-a) e_a`; coordinate `i` is `e_(i+1)`. -/
abbrev weightedModule (n : ℕ) := Fin n → A

def inWeightedModule (n : ℕ) (f : weightedModule n) : Prop :=
  ∀ i : Fin n, weightedHomogeneous (n - (i.val + 1)) (f i)

/-- The direct-sum carrier `M_n`, presented as its exact homogeneous-function set. -/
def M (n : ℕ) : Set (weightedModule n) := {f | inWeightedModule n f}

def rootSize {n : ℕ} (i : Fin n) : ℕ := i.val + 1

def deletedWeight {n : ℕ} (i : Fin n) : ℕ := n - rootSize i

def coordinateMonomial {n : ℕ} (i : Fin n) (m : ℕ →₀ ℕ) : weightedModule n :=
  fun j => if j = i then MvPolynomial.monomial m 1 else 0

def tau (n : ℕ) (f : weightedModule n) : A :=
  ∑ i : Fin n, partVar (i.val + 1) * f i

def iota (n : ℕ) (Q : Polynomial A) : weightedModule n :=
  fun i => Q.coeff (n - (i.val + 1))

def truncatedWeightedSeries (n : ℕ) (Q : Polynomial A) : Prop :=
  (∀ k < n, weightedHomogeneous k (Q.coeff k)) ∧
    (∀ k, n ≤ k → Q.coeff k = 0)

abbrev Partition (n : ℕ) := {m : ℕ →₀ ℕ // weightedDegree m = n}

def partSupport {n : ℕ} (μ : Partition n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => μ.1 i.val ≠ 0)

abbrev SupportedRoot {n : ℕ} (μ : Partition n) :=
  {i : Fin n // i ∈ partSupport μ}

def canonicalBase {n : ℕ} (μ : Partition n) (b : Fin n) : Prop :=
  b ∈ partSupport μ ∧ ∀ i ∈ partSupport μ, b ≤ i

def basisElement {n : ℕ} (μ : Partition n) (a : SupportedRoot μ) : weightedModule n :=
  fun i =>
    if i = a.1 then
      MvPolynomial.monomial
        (μ.1 - Finsupp.single a.1.val 1) 1
    else 0

def blockCombination {n : ℕ} (μ : Partition n)
    (c : SupportedRoot μ → ℤ) : weightedModule n :=
  ∑ a : SupportedRoot μ, fun i =>
    (c a : A) * basisElement μ a i

def augmentation {n : ℕ} {μ : Partition n}
    (c : SupportedRoot μ → ℤ) : ℤ :=
  ∑ a : SupportedRoot μ, c a

def canonicalExpansion {n : ℕ} {μ : Partition n}
    (b : SupportedRoot μ) (c : SupportedRoot μ → ℤ) : weightedModule n :=
  ∑ a ∈ (Finset.univ.filter (fun a : SupportedRoot μ => a ≠ b)),
    fun i => (c a : A) * (basisElement μ a i - basisElement μ b i)

def quotientMonomial {n : ℕ} {μ : Partition n}
    (a b : SupportedRoot μ) : A :=
  MvPolynomial.monomial
    (μ.1 - Finsupp.single a.1.val 1 - Finsupp.single b.1.val 1) 1

def koszulDifference {n : ℕ} {μ : Partition n}
    (a b : SupportedRoot μ) : weightedModule n :=
  fun i =>
    quotientMonomial a b *
      (if i = a.1 then partVar (b.1.val + 1)
       else if i = b.1 then -partVar (a.1.val + 1)
       else 0)

def rawPartSupport (n : ℕ) (m : ℕ →₀ ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => m i.val ≠ 0)

abbrev RawSupportedRoot (n : ℕ) (m : ℕ →₀ ℕ) :=
  {i : Fin n // i ∈ rawPartSupport n m}

def rawBasisElement (n : ℕ) (m : ℕ →₀ ℕ)
    (a : RawSupportedRoot n m) : weightedModule n :=
  fun i =>
    if i = a.1 then
      MvPolynomial.monomial (m - Finsupp.single a.1.val 1) 1
    else 0

def rawBlockCombination (n : ℕ) (m : ℕ →₀ ℕ)
    (c : RawSupportedRoot n m → ℤ) : weightedModule n :=
  ∑ a : RawSupportedRoot n m, fun i =>
    (c a : A) * rawBasisElement n m a i

def rawBlockKernel (n : ℕ) (m : ℕ →₀ ℕ) (v : weightedModule n) : Prop :=
  weightedDegree m = n ∧
    ∃ c : RawSupportedRoot n m → ℤ,
      (∑ a : RawSupportedRoot n m, c a) = 0 ∧
        v = rawBlockCombination n m c

def partitionSupportOf (n : ℕ) (f : weightedModule n) : Finset (ℕ →₀ ℕ) := by
  classical
  exact (Finset.univ.biUnion (fun i : Fin n =>
    (f i).support.image (fun m => m + Finsupp.single i.val 1)))

def partitionwiseKernelDirectSum (n : ℕ) : Prop :=
  ∀ f : weightedModule n, f ∈ M n →
    (tau n f = 0 ↔
      ∃ v : Finsupp (ℕ →₀ ℕ) (weightedModule n),
        (∀ m ∈ v.support, rawBlockKernel n m (v m)) ∧
          f = v.sum (fun _ z => z)) ∧
    (∀ v w : Finsupp (ℕ →₀ ℕ) (weightedModule n),
      (∀ m ∈ v.support, rawBlockKernel n m (v m)) →
      (∀ m ∈ w.support, rawBlockKernel n m (w m)) →
      v.sum (fun _ z => z) = w.sum (fun _ z => z) → v = w)

def lowerVariableIdeal (a : ℕ) : Ideal A :=
  Ideal.span {p : A | ∃ b, 1 ≤ b ∧ b < a ∧ p = partVar b}

def firstNonzeroIndex (n : ℕ) (D : Polynomial A) (r : Fin n) : Prop :=
  D.coeff r.val ≠ 0 ∧ ∀ k < r.val, D.coeff k = 0

def firstRowMonomialFactor {n : ℕ} (D : Polynomial A) (r : Fin n)
    (a : ℕ) (m : ℕ →₀ ℕ) (b : ℕ) (h : ℕ →₀ ℕ) : Prop :=
  1 ≤ b ∧ b < a ∧ m = h + Finsupp.single (b - 1) 1 ∧
    m ∈ (D.coeff r.val).support

def compensatingTerm (n a b : ℕ) (h : ℕ →₀ ℕ) (c : ℤ) : weightedModule n :=
  fun i =>
    if i.val + 1 = b then
      -(c : A) * partVar a * MvPolynomial.monomial h 1
    else 0

def rationalizeHom : A →+* Aℚ :=
  MvPolynomial.map (Int.castRingHom ℚ)

def rationalize (p : A) : Aℚ := rationalizeHom p

def rationalizePolynomial (Q : Polynomial A) : Polynomial Aℚ :=
  Q.map rationalizeHom

def logarithmicQuotientCoefficient (r : ℕ)
    (Qplus Qminus : Polynomial A) : Aℚ :=
  PowerSeries.coeff r
    (PowerSeries.logOf
      (((rationalizePolynomial Qplus : PowerSeries Aℚ) *
        PowerSeries.invOfUnit
          (rationalizePolynomial Qminus : PowerSeries Aℚ) (1 : Aℚˣ))))

def constantTermOne (Q : Polynomial A) : Prop := Q.coeff 0 = 1

def firstPolynomialDifference (r : ℕ) (Qplus Qminus : Polynomial A) : Prop :=
  Qplus.coeff r ≠ Qminus.coeff r ∧
    ∀ k < r, Qplus.coeff k = Qminus.coeff k

/-- Claim 47551: the weight-`n` monomial blocks are integral augmentations,
with the canonical minimum-root Koszul expansion and the partitionwise direct sum. -/
def claim47551_partitionwiseAugmentationKernel : Prop :=
  (∀ n : ℕ, 0 < n → ∀ μ : Partition n,
    (∃ b : Fin n, canonicalBase μ b) ∧
    (∀ i : Fin n, ∀ m : ℕ →₀ ℕ,
      weightedDegree m = n - rootSize i →
        ∃ μ : ℕ →₀ ℕ, weightedDegree μ = n ∧
          ∃ a : RawSupportedRoot n μ,
            a.1 = i ∧
              rawBasisElement n μ a = coordinateMonomial i m) ∧
    (∀ a : SupportedRoot μ,
      tau n (basisElement μ a) = MvPolynomial.monomial μ.1 1) ∧
    (∀ c : SupportedRoot μ → ℤ,
      tau n (blockCombination μ c) =
        (augmentation c : A) * MvPolynomial.monomial μ.1 1 ∧
      (tau n (blockCombination μ c) = 0 ↔ augmentation c = 0)) ∧
    (∀ b : SupportedRoot μ, canonicalBase μ b →
      ∀ c : SupportedRoot μ → ℤ, augmentation c = 0 →
        blockCombination μ c = canonicalExpansion b c) ∧
    (∀ a b : SupportedRoot μ, a ≠ b →
      basisElement μ a - basisElement μ b = koszulDifference a b)) ∧
  (∀ n : ℕ, partitionwiseKernelDirectSum n)

/-- Claim 47552: the minimum support root is the canonical integral correction
root, and every correction is strictly upward in deleted weight. -/
def claim47552_strictUpwardIntegralContraction : Prop :=
  ∀ n : ℕ, 0 < n → ∀ μ : Partition n,
    ∀ b : SupportedRoot μ, canonicalBase μ b.1 →
      ∀ a : SupportedRoot μ, a ≠ b →
        rootSize b.1 < rootSize a.1 ∧
        deletedWeight b.1 > deletedWeight a.1 ∧
        (∀ c : SupportedRoot μ → ℤ,
          augmentation c = 0 →
            blockCombination μ c = canonicalExpansion b c)

/-- Claim 47553: the first unresolved coefficient is divisible by the lower
variables, and the same first-order defect is visible after taking logarithms. -/
def claim47553_firstDefectIdealAndLogarithm : Prop :=
  (∀ n : ℕ, 0 < n → ∀ D : Polynomial A,
    truncatedWeightedSeries n D →
    ∀ r : Fin n, firstNonzeroIndex n D r →
      tau n (iota n D) = 0 →
      let a := n - r.val
      (D.coeff r.val ∈ lowerVariableIdeal a) ∧
        (∀ m ∈ (D.coeff r.val).support,
          ∃ b : ℕ, ∃ h : ℕ →₀ ℕ,
            firstRowMonomialFactor D r a m b h ∧
            weightedDegree h = r.val - b ∧
            n - b > r.val ∧
            ∃ c : ℤ, c = (D.coeff r.val).coeff m ∧ c ≠ 0 ∧
              (MvPolynomial.monomial m c : A) =
                partVar b * MvPolynomial.monomial h c ∧
              compensatingTerm n a b h c =
              fun i => if i.val + 1 = b then
                -(c : A) * partVar a * MvPolynomial.monomial h 1 else 0)) ∧
  (∀ r : ℕ, ∀ Qplus Qminus : Polynomial A,
    constantTermOne Qplus → constantTermOne Qminus →
    firstPolynomialDifference r Qplus Qminus →
      rationalize (Qplus.coeff r - Qminus.coeff r) =
        logarithmicQuotientCoefficient r Qplus Qminus)

end

end MathlibPlus.Open.ResearchFormalization.R3664
