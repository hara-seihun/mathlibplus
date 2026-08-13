import Mathlib
import MathlibPlus.Analysis.Claim4805

open scoped BigOperators
open Polynomial

namespace MathlibPlus.Open.NewResearch2.AlternantCharlier

noncomputable section

private def centralCharlier : ℕ → Polynomial ℚ :=
  MathlibPlus.Analysis.Claim4805.centralCharlierPolynomial_claim4805

private def realCentralCharlier : ℕ → Polynomial ℝ :=
  fun n ↦ (centralCharlier n).map (algebraMap ℚ ℝ)

/-- Claim 4790: divisibility of an exterior alternant by the Vandermonde
produces a symmetric normalized quotient. -/
def claim4790_normalizedExteriorAlternant
    (r : ℕ) (J : Fin r → ℕ) (F : ℕ → Polynomial ℝ) : Prop :=
  let delta : (Fin r → ℝ) → ℝ := fun y ↦
    Matrix.det (fun i j : Fin r ↦ y i ^ (j : ℕ))
  let alternant : (Fin r → ℝ) → ℝ := fun y ↦
    Matrix.det (fun i j : Fin r ↦ (F (J j)).eval (y i))
  StrictMono J ∧
    ∃ Q : (Fin r → ℝ) → ℝ,
      (∀ y, alternant y = delta y * Q y) ∧
      (∀ (σ : Equiv.Perm (Fin r)) (y : Fin r → ℝ),
        Q (y ∘ σ) = Q y)

/-- Claim 4791: exact Schur expansion of the normalized alternant, with the
coefficient minors indexed by the packet M. -/
def claim4791_exactExteriorSchurExpansion
    (r : ℕ) (J : Fin r → ℕ) (F : ℕ → Polynomial ℝ)
    (S : (Fin r → ℝ) → ℝ) (c : List ℕ → ℝ)
    (schur : List ℕ → (Fin r → ℝ) → ℝ)
    (A : ℕ → Fin r → ℝ) (M : List ℕ → Fin r → ℕ)
    (isPartition : List ℕ → Prop) : Prop :=
  let delta : (Fin r → ℝ) → ℝ := fun y ↦
    Matrix.det (fun i j : Fin r ↦ y i ^ (j : ℕ))
  let alternant : (Fin r → ℝ) → ℝ := fun y ↦
    Matrix.det (fun i j : Fin r ↦ (F (J j)).eval (y i))
  StrictMono J ∧
    (∀ part, ¬ isPartition part → c part = 0) ∧
    (∀ part, c part = Matrix.det (fun i j : Fin r ↦ A (M part i) j)) ∧
    ∀ y, delta y ≠ 0 →
      S y = alternant y / delta y ∧
        S y = ∑' part : List ℕ, c part * schur part y

/-- Claim 4793: an arithmetic band packet is a value in each prescribed
arithmetic band. -/
def claim4793_arithmeticBandPacket
    (r : ℕ) (bands : ℕ → Set ℝ) (bandIndex : Fin r → ℕ)
    (y : Fin r → ℝ) : Prop :=
  ∀ i, y i ∈ bands (bandIndex i)

/-- Claim 4794: the arithmetic band--Schur cone is positivity on every band
packet. -/
def claim4794_arithmeticBandSchurCone
    (r : ℕ) (bands : ℕ → Set ℝ) (S : (Fin r → ℝ) → ℝ) : Prop :=
  ∀ (bandIndex : Fin r → ℕ) (y : Fin r → ℝ),
    claim4793_arithmeticBandPacket r bands bandIndex y → 0 < S y

/-- Claim 4795: coefficientwise nonnegativity, together with the nonnegative
Schur evaluations and a positive term on every packet, implies band-Schur
positivity. -/
def claim4795_coefficientwiseNonnegativityImpliesBandSchurPositivity
    (r : ℕ) (bands : ℕ → Set ℝ) (S : (Fin r → ℝ) → ℝ)
    (c : List ℕ → ℝ) (schur : List ℕ → (Fin r → ℝ) → ℝ) : Prop :=
  ((∀ part, 0 ≤ c part) ∧
    (∃ part, 0 < c part) ∧
    (∀ part bandIndex y,
      claim4793_arithmeticBandPacket r bands bandIndex y →
        0 ≤ schur part y) ∧
    (∀ part bandIndex y,
      claim4793_arithmeticBandPacket r bands bandIndex y →
        0 < c part → 0 < schur part y) ∧
    (∀ y, S y = ∑' part : List ℕ, c part * schur part y)) →
    claim4794_arithmeticBandSchurCone r bands S

/-- Claim 4796: band-Schur positivity can hold with a negative Schur
coefficient. -/
def claim4796_bandSchurConeStrictlyLargerThanCoefficientCone
    (r : ℕ) (bands : ℕ → Set ℝ)
    (schur : List ℕ → (Fin r → ℝ) → ℝ) : Prop :=
  ∃ (S : (Fin r → ℝ) → ℝ) (c : List ℕ → ℝ),
    claim4794_arithmeticBandSchurCone r bands S ∧
      (∃ part, c part < 0) ∧
      (∀ y, S y = ∑' part : List ℕ, c part * schur part y)

/-- Claim 4797: after fixing one common ambient function space and domain, the
band-Schur cone is a proper intermediate cone. -/
def claim4797_bandSchurPositivityIntermediate
    (r : ℕ)
    (coefficientCone bandCone pointwiseCone : Set ((Fin r → ℝ) → ℝ)) : Prop :=
  coefficientCone ⊂ bandCone ∧ bandCone ⊂ pointwiseCone

/-- Claim 4799: the central Charlier family is given by the displayed
recurrence with a=5/4. -/
def claim4799_centralCharlierPolynomialRecurrence : Prop :=
  centralCharlier 0 = 1 ∧
    ∀ k : ℕ,
      centralCharlier (k + 1) =
        Polynomial.X * Polynomial.derivative (centralCharlier k) +
          (Polynomial.C (5 / 4) - Polynomial.X) * centralCharlier k

/-- Claim 4800: Euler-operator representation of the central Charlier family. -/
def claim4800_eulerOperatorRepresentation : Prop :=
  let theta : (ℝ → ℝ) → ℝ → ℝ := fun f q ↦ q * deriv f q
  let A : (ℝ → ℝ) → ℝ → ℝ :=
    fun f q ↦ (5 / 4 : ℝ) * f q + theta f q
  ∀ k : ℕ, ∀ q : ℝ,
    (realCentralCharlier k).eval q =
      Real.exp q * ((A^[k]) (fun x : ℝ ↦ Real.exp (-x))) q

/-- Claim 4801: exponential generating function. -/
def claim4801_exponentialGeneratingFunction : Prop :=
  ∀ q t : ℝ,
    HasSum (fun k : ℕ ↦
      (realCentralCharlier k).eval q * t ^ k / (Nat.factorial k : ℝ))
      (Real.exp ((5 / 4 : ℝ) * t + q * (1 - Real.exp t)))

/-- Claim 4802: the negative-intensity Poisson/umbral formula. -/
def claim4802_negativeIntensityPoissonFormula : Prop :=
  ∀ k : ℕ, ∀ q : ℝ,
    (realCentralCharlier k).eval q = Real.exp q *
      ∑' n : ℕ,
        ((-q) ^ n / (Nat.factorial n : ℝ)) * ((5 / 4 : ℝ) + n) ^ k

/-- Claim 4803: even derivatives of the folded kernel at the wall. -/
def claim4803_foldedKernelJetIdentity
    (K : ℝ → ℝ → ℝ) : Prop :=
  ∀ j : ℕ, ∀ q : ℝ,
    iteratedDeriv (2 * j) (K q) 0 =
      2 * 4 ^ j * Real.exp (-q) * (realCentralCharlier (2 * j)).eval q

private def centralCharlierRootData (k : ℕ) : Prop :=
  ∃ ρ : ℕ → ℝ,
    (∀ i, i < k → 0 < ρ i) ∧
    (∀ i j, i < k → j < k → i < j → ρ i < ρ j) ∧
    (∀ i, i < k →
      (realCentralCharlier k).derivative.eval (ρ i) ≠ 0) ∧
    ∀ x : ℝ, (realCentralCharlier k).eval x = 0 ↔
      ∃ i, i < k ∧ x = ρ i

/-- Claim 4807: every positive-degree central Charlier polynomial has exactly
k distinct simple positive real zeros. -/
def claim4807_simplePositiveRootTheorem : Prop :=
  ∀ k : ℕ, 1 ≤ k → centralCharlierRootData k

/-- Claim 4808: consecutive central Charlier zeros strictly interlace. -/
def claim4808_strictConsecutiveInterlacing : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    ∃ ρ : ℕ → ℝ,
      (∀ i, i < k → 0 < ρ i) ∧
      (∀ i j, i < k → j < k → i < j → ρ i < ρ j) ∧
      (∀ x : ℝ, (realCentralCharlier k).eval x = 0 ↔
        ∃ i, i < k ∧ x = ρ i) ∧
      (∀ x : ℝ, (realCentralCharlier (k + 1)).eval x = 0 →
        (0 < x ∧ x < ρ 0) ∨
          (∃ i, i + 1 < k ∧ ρ i < x ∧ x < ρ (i + 1)) ∨
          ρ (k - 1) < x) ∧
      (∃ x, (realCentralCharlier (k + 1)).eval x = 0 ∧
        0 < x ∧ x < ρ 0) ∧
      (∀ i, i + 1 < k →
        ∃ x, (realCentralCharlier (k + 1)).eval x = 0 ∧
          ρ i < x ∧ x < ρ (i + 1)) ∧
      (∃ x, (realCentralCharlier (k + 1)).eval x = 0 ∧
        ρ (k - 1) < x)

/-- Claim 4810: the even central-Charlier Wronskian. -/
def claim4810_evenCentralCharlierWronskian
    (r : ℕ) (C : ℕ → ℝ → ℝ) : Prop :=
  ∀ q : ℝ,
    C r q = Matrix.det
      (fun i j : Fin r ↦
        iteratedDeriv (i : ℕ)
          (fun x : ℝ ↦ (realCentralCharlier (2 * (j : ℕ))).eval x) q)

/-- Claim 4811: exact degree of the even central-Charlier Wronskian. -/
def claim4811_evenCentralCharlierWronskianDegree : Prop :=
  ∀ r : ℕ,
    let C : Polynomial ℚ := Matrix.det
      (fun i j : Fin r ↦
        (Polynomial.derivative^[i])
          (centralCharlier (2 * (j : ℕ))))
    C.natDegree = r * (r - 1) / 2

/-- Claim 4812: all lower wall jets vanish and the first nonzero jet is a
positive constant multiple of the even Wronskian. -/
def claim4812_firstNonzeroCoalescedWallJet
    (W : ℕ → ℝ → ℝ → ℝ) (C : ℕ → ℝ → ℝ) : Prop :=
  ∀ r : ℕ, ∃ c : ℝ, 0 < c ∧ ∀ q : ℝ,
    (∀ j : ℕ, j < r * (r - 1) / 2 →
      iteratedDeriv j (W r · q) 0 = 0) ∧
    iteratedDeriv (r * (r - 1) / 2) (W r · q) 0 = c * C r q

/-- Claim 4814: the moment determinant identity as an identity of
polynomials. -/
def claim4814_momentDeterminantIdentity
    (M : ℕ → ℕ → Polynomial ℝ) (C : ℕ → Polynomial ℝ) : Prop :=
  ∀ r : ℕ,
    Polynomial.X ^ (r * (r - 1) / 2) * C r =
      Matrix.det (fun i j : Fin r ↦ M (i : ℕ) (j : ℕ))

/-- Claim 4816: sixth wall jet at rank four. -/
def claim4816_sixthWallJetRankFour
    (W4 : ℝ → ℝ → ℝ) (C4 : ℝ → ℝ) : Prop :=
  ∀ q : ℝ, iteratedDeriv 6 (W4 · q) 0 = 48 * C4 q

/-- Claim 4817: the rank-four wall polynomial has exactly two positive roots;
the stated decimal values are represented by exact rational isolating
intervals, and the larger root is below 4π. -/
def claim4817_positiveRootCountRankFourWallPolynomial
    (C4 : Polynomial ℝ) : Prop :=
  ∃ ρ₁ ρ₂ : ℝ,
    0 < ρ₁ ∧ ρ₁ < ρ₂ ∧
    (16782052469 : ℝ) / 10 ^ 10 < ρ₁ ∧
      ρ₁ < (16782052470 : ℝ) / 10 ^ 10 ∧
    (536113359988346505777 : ℝ) / 10 ^ 20 < ρ₂ ∧
      ρ₂ < (536113359988346505778 : ℝ) / 10 ^ 20 ∧
    ρ₂ < 4 * Real.pi ∧
    (∀ x : ℝ, 0 < x → (C4.eval x = 0 ↔ x = ρ₁ ∨ x = ρ₂))

/-- Claim 4818: exact rational isolating intervals for the two positive roots. -/
def claim4818_numericalIsolationsTwoPositiveRoots
    (C4 : Polynomial ℝ) : Prop :=
  ∃ ρ₁ ρ₂ : ℝ,
    C4.eval ρ₁ = 0 ∧ C4.eval ρ₂ = 0 ∧
    (16782052469 : ℝ) / 10 ^ 10 < ρ₁ ∧
      ρ₁ < (16782052470 : ℝ) / 10 ^ 10 ∧
    (536113359988346505777 : ℝ) / 10 ^ 20 < ρ₂ ∧
      ρ₂ < (536113359988346505778 : ℝ) / 10 ^ 20

/-- Claim 4820: the rank-three wall polynomial has the unique real root in
the stated exact rational isolating interval. -/
def claim4820_uniqueRealRootRankThree
    (C3 : Polynomial ℝ) : Prop :=
  ∃ ρ : ℝ,
    C3.eval ρ = 0 ∧
    (352707460930038659024 : ℝ) / 10 ^ 20 < ρ ∧
      ρ < (352707460930038659025 : ℝ) / 10 ^ 20 ∧
    ∀ x : ℝ, C3.eval x = 0 ↔ x = ρ

/-- Claim 4821: partition-confluent polarization quotient. -/
def claim4821_partitionConfluentPolarizationQuotient
    (r : ℕ) (P : ℕ → Polynomial ℝ)
    (polarization : (Fin (r - 1) → ℝ) → ℝ)
    (x : Fin (r - 1) → ℝ) : Prop :=
  polarization x =
    ((∏ j : Fin (r - 1), (Nat.factorial (j : ℕ) : ℝ)) *
      Matrix.det (fun i j : Fin (r - 1) ↦
        (P (2 * (j : ℕ))).derivative.eval (x i))) /
      Matrix.det (fun i j : Fin (r - 1) ↦ x i ^ (j : ℕ))

/-- Claim 4823: on the full diagonal, the polarization equals the even
central-Charlier Wronskian. -/
def claim4823_diagonalConfluentIdentity
    (r : ℕ) (polarization : (Fin (r - 1) → ℝ) → ℝ) : Prop :=
  ∀ q : ℝ,
    polarization (fun _ : Fin (r - 1) ↦ q) =
      Matrix.det
        (fun i j : Fin r ↦
          ((Polynomial.derivative^[i])
            (realCentralCharlier (2 * (j : ℕ)))).eval q)

/-- Claim 4824: nonzero polarization minors are exactly the strictly ordered
exponent sets satisfying the staircase bounds. -/
def claim4824_staircaseCriterionForNonzeroSchurMinors
    (d : ℕ) (A : ℕ → Fin d → ℝ) : Prop :=
  ∀ K : Fin d → ℕ,
    Matrix.det (fun i j : Fin d ↦ A (K i) j) ≠ 0 ↔
      StrictMono K ∧
        ∀ i : Fin d, K i ≤ 2 * ((i : ℕ) + 1) - 1

/-- Claim 4826: the 4^n-rescaled rational columns have integral coefficients and
the displayed recurrence. -/
def claim4826_integralColumnRecurrence
    (P : ℕ → Polynomial ℚ) : Prop :=
  let Q : ℕ → Polynomial ℚ := fun n ↦ (4 : ℚ) ^ n • P n
  (∀ n : ℕ,
    Q (n + 1) = 4 * Polynomial.X * (Q n).derivative +
      (5 - 4 * Polynomial.X) * Q n) ∧
    (∀ n k : ℕ, ∃ z : ℤ, (Q n).coeff k = (z : ℚ))

/-- Claim 4828: the evaluation nodes are the nonnegative square shifts. -/
def claim4828_nonnegativeSquareShiftNodes
    (u : ℝ) (X : ℕ → ℝ) (x : ℕ → ℝ) : Prop :=
  0 ≤ u ∧ (∀ i, 0 ≤ X i) ∧
    ∀ i : ℕ, x i = (2 + u) * i ^ 2 + X i

/-- The finite Lagrange divided difference on the first `i` nodes. -/
private def nr2_dividedDifference
    (g : ℝ → ℝ) (x : ℕ → ℝ) (i : ℕ) : ℝ :=
  if 0 < i then
    ∑ k : Fin i,
      g (x (k : ℕ)) /
        ∏ l : Fin i,
          if l = k then 1 else x (k : ℕ) - x (l : ℕ)
  else 0

/-- Claim 4829: the lower Newton array consists of these divided differences. -/
def claim4829_newtonDividedDifferenceArray
    (g : ℕ → ℝ → ℝ) (x : ℕ → ℝ) (A : ℕ → ℕ → ℝ) : Prop :=
  ∀ i j : ℕ, A i j = nr2_dividedDifference (g j) x (i + 1)

/-- Claim 4830: successive Newton divided-difference rows remove the
Vandermonde. -/
def claim4830_vandermondeRemovalByNewtonRows
    (n : ℕ) (g : ℕ → ℝ → ℝ) (x : ℕ → ℝ)
    (hDistinct : ∀ i j, i < n → j < n → i ≠ j → x i ≠ x j) : Prop :=
  Matrix.det (fun i j : Fin n ↦ g (j : ℕ) (x (i : ℕ))) =
    Matrix.det (fun i j : Fin n ↦ x (i : ℕ) ^ (j : ℕ)) *
      Matrix.det (fun i j : Fin n ↦
        nr2_dividedDifference (g (j : ℕ)) x ((i : ℕ) + 1))

/-- Claim 4831: monomial coefficients expand divided differences in complete
homogeneous functions of the initial nodes. -/
def claim4831_monomialToCompleteHomogeneousExpansion
    (n : ℕ) (g : Fin n → Polynomial ℝ) (x : ℕ → ℝ) : Prop :=
  let h : ℕ → ℕ → ℝ := fun m i ↦
    ∑ e : Fin i → Fin (m + 1),
      if (∑ k : Fin i, (e k : ℕ)) = m then
        ∏ k : Fin i, x (k : ℕ) ^ (e k : ℕ)
      else 0
  ∀ i : ℕ, 1 ≤ i → ∀ j : Fin n,
    nr2_dividedDifference (fun z ↦ (g j).eval z) x i =
      ∑' k : {k : ℕ // i - 1 ≤ k},
        (g j).coeff k * h (k.1 - (i - 1)) i

/-- Claim 4833: multiplicity profiles form the coordinatewise lattice based at
quadratic anchors, with single-coordinate edges. -/
def claim4833_multiplicityProfileLattice : Prop :=
  let anchor : ℕ → ℕ := fun i ↦ 2 * i ^ 2
  let node : (ℕ →₀ ℕ) → ℕ → ℕ := fun m i ↦ anchor i + m i
  (∀ m n : ℕ →₀ ℕ,
    m ≤ n ↔ ∃ d : ℕ →₀ ℕ, n = m + d) ∧
    (∀ m : ℕ →₀ ℕ, ∀ i : ℕ,
      node (m + Finsupp.single i 1) i = node m i + 1 ∧
        ∀ j, j ≠ i → node (m + Finsupp.single i 1) j = node m j)

/-- Claim 4835: scalar connection along a profile edge. -/
def claim4835_edgeConnection
    (H : (ℕ →₀ ℕ) → ℝ) (ω : ℕ → (ℕ →₀ ℕ) → ℝ) : Prop :=
  ∀ i m, H m ≠ 0 →
    ω i m = H (m + Finsupp.single i 1) / H m

/-- Claim 4836: the scalar edge connection is flat around every nonzero
coordinate square. -/
def claim4836_flatnessOfScalarEdgeConnection
    (H : (ℕ →₀ ℕ) → ℝ) (ω : ℕ → (ℕ →₀ ℕ) → ℝ) : Prop :=
  ∀ i j m, i ≠ j →
    H m ≠ 0 ∧ H (m + Finsupp.single i 1) ≠ 0 ∧
      H (m + Finsupp.single j 1) ≠ 0 →
    ω i m * ω j (m + Finsupp.single i 1) =
      ω j m * ω i (m + Finsupp.single j 1) ∧
    ω i m * ω j (m + Finsupp.single i 1) =
      H (m + Finsupp.single i 1 + Finsupp.single j 1) / H m

/-- Claim 4837: the unnormalized two-direction Desnanot--Jacobi diamond. -/
def claim4837_nonScalarDesnanotJacobiDiamond
    (Δ : (ℕ →₀ ℕ) → ℝ) (D : ℕ → ℕ → (ℕ →₀ ℕ) → ℝ)
    (B : ℕ → ℕ → (ℕ →₀ ℕ) → ℝ) : Prop :=
  ∀ i j m,
    D i j m * Δ m = B i 1 m * B j 2 m - B i 2 m * B j 1 m

/-- Claim 4838: one free knot gives the stated residual chart. -/
def claim4838_oneFreeKnotResidualChart
    (H : ℕ → (ℕ →₀ ℕ) → ℝ → ℝ)
    (Hbase : ℕ → (ℕ →₀ ℕ) → ℝ)
    (R : ℕ → (ℕ →₀ ℕ) → ℝ → ℝ) : Prop :=
  ∀ j m q, Hbase (j - 1) m ≠ 0 →
    R j m q = H j m q / Hbase (j - 1) m

/-- Claim 4843: knot insertion acts on all exterior degrees by the direct sum
of the compound matrices.  The packet and ordering maps give the canonical
k-subset exterior basis without changing the carrier. -/
def claim4843_compoundTransferOnFullExteriorFrame
    (N : ℕ) (T : ℝ → Matrix (Fin N) (Fin N) ℝ)
    (packet : ∀ k : Fin (N + 1),
      Fin (Nat.choose N k.1) → {s : Finset (Fin N) // s.card = k.1})
    (packetOrder : ∀ k : Fin (N + 1),
      ∀ I : Fin (Nat.choose N k.1), Fin k.1 → Fin N)
    (action : ℝ →
      (∀ k : Fin (N + 1), Fin (Nat.choose N k.1) → ℝ) →
      (∀ k : Fin (N + 1), Fin (Nat.choose N k.1) → ℝ)) : Prop :=
  ∀ (z : ℝ) (v : ∀ k : Fin (N + 1),
      Fin (Nat.choose N k.1) → ℝ)
    (k : Fin (N + 1)) (I : Fin (Nat.choose N k.1)),
    action z v k I =
      ∑ J : Fin (Nat.choose N k.1),
        Matrix.det (fun i j : Fin k.1 ↦
          T z (packetOrder k I i) (packetOrder k J j)) * v k J

private def nr2_matrixProduct
    {N : ℕ} (T : ℝ → Matrix (Fin N) (Fin N) ℝ) :
    (m : ℕ) → (Fin m → ℝ) → Matrix (Fin N) (Fin N) ℝ
  | 0, _ => 1
  | m + 1, z => nr2_matrixProduct T m (fun i => z i.succ) * T (z 0)

/-- Claim 4844: products of compounds are the corresponding skew-Schur
packets. -/
def claim4844_compoundProductsAreSkewSchurPackets
    (N k m : ℕ) (T : ℝ → Matrix (Fin N) (Fin N) ℝ)
    (subsetToPartition : (Fin k → Fin N) → List ℕ)
    (skewSchur : List ℕ → List ℕ → MvPolynomial (Fin m) ℝ) : Prop :=
  ∀ (z : Fin m → ℝ) (I J : Fin k → Fin N),
    StrictMono I → StrictMono J →
    Matrix.det (fun i j : Fin k ↦
      nr2_matrixProduct T m z (I i) (J j)) =
      MvPolynomial.eval z (skewSchur (subsetToPartition I) (subsetToPartition J))

/-- Claim 4848: Jacobi knot insertion factors into descending elementary chips. -/
def claim4848_jacobiChipFactorization
    (N : ℕ) (T : ℝ → Matrix (Fin N) (Fin N) ℝ) : Prop :=
  let I : Matrix (Fin N) (Fin N) ℝ := 1
  let E : ℕ → Matrix (Fin N) (Fin N) ℝ :=
    fun i r c ↦ if r.1 = i + 1 ∧ c.1 = i then 1 else 0
  let chip : ℕ → ℝ → Matrix (Fin N) (Fin N) ℝ :=
    fun i z ↦ I + z • E i
  ∀ z : ℝ,
    T z = List.foldl (fun U i ↦ chip i z * U) I (List.range (N - 1))

end
end MathlibPlus.Open.NewResearch2.AlternantCharlier
