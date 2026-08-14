import Mathlib

open scoped BigOperators Interval Topology
open Filter

namespace MathlibPlus.Open.ResearchFormalization

noncomputable section

/-- The exact permutation-invariance assertion for the two-element cyclic group. -/
def claim59807 : Prop :=
  ∀ (S T : Set (ZMod 2)),
    0 ∉ S →
    0 ∉ T →
    ∀ e : Equiv.Perm (ZMod 2),
      (∀ x y : ZMod 2, x - y ∈ S ↔ e x - e y ∈ T) →
      S = T

/-- The determinant sequence in the consecutive Vandermonde family. -/
def vandermondeV (n : ℕ) : ℚ :=
  Matrix.det (fun i j : Fin n => ((i.1 : ℕ) : ℚ) ^ j.1)

/-- The coefficient sequence specified by the two determinant formulas. -/
def coefficientC : ℕ → ℚ
  | 0 => vandermondeV 2 / 2
  | n + 1 => (2 : ℚ) ^ n * vandermondeV (n + 3)

def claim59809 : Prop :=
  (∀ n : ℕ,
    vandermondeV n = Finset.prod (Finset.range n) (fun k => ((Nat.factorial k : ℕ) : ℚ))) ∧
  (∀ n : ℕ,
    vandermondeV (n + 1) = ((Nat.factorial n : ℕ) : ℚ) * vandermondeV n) ∧
  coefficientC 0 = vandermondeV 2 / 2 ∧
  coefficientC 0 = (1 : ℚ) / 2 ∧
  (∀ n : ℕ,
    coefficientC (n + 1) = (2 : ℚ) ^ n * vandermondeV (n + 3)) ∧
  (∀ n : ℕ,
    coefficientC (n + 1) =
      (2 : ℚ) * ((Nat.factorial (n + 2) : ℕ) : ℚ) * coefficientC n) ∧
  (∀ r : ℕ, 3 ≤ r →
    coefficientC (r - 2) =
      (2 : ℚ) ^ (r - 3) *
        Finset.prod (Finset.Icc 2 (r - 1))
          (fun k => ((Nat.factorial k : ℕ) : ℚ))) ∧
  (∀ r : ℕ, 3 ≤ r →
    vandermondeV (r - 1) =
      ((Nat.factorial (r - 2) : ℕ) : ℚ) * vandermondeV (r - 2)) ∧
  coefficientC 0 = (1 : ℚ) / 2 ∧
  coefficientC 1 = 2 ∧
  coefficientC 2 = 24 ∧
  coefficientC 3 = 1152 ∧
  coefficientC 4 = 276480 ∧
  coefficientC 5 = 398131200


def primeSeriesTerm (p : ℕ) (t : ℝ) (k : ℕ) : ℂ :=
  Complex.ofReal
      (Real.log (p : ℝ) /
        Real.rpow (p : ℝ) (((k + 1 : ℕ) : ℝ) / 2)) *
    Complex.exp
      (-Complex.I * ((k + 1 : ℕ) : ℂ) * (t : ℂ) *
        Complex.ofReal (Real.log (p : ℝ)))

def primeSeries (p : ℕ) (t : ℝ) : ℂ :=
  tsum (fun k : ℕ => primeSeriesTerm p t k)

def finitePrimeSeries (P : Finset ℕ) (t : ℝ) : ℂ :=
  Finset.sum P (fun p => primeSeries p t)

def collisionIndex (a b : ℕ) :=
  (Fin a → ℕ) × (Fin b → ℕ) × (Fin a → ℕ) × (Fin b → ℕ)

def collisionTerm (P : Finset ℕ) (a b : ℕ)
    (z : collisionIndex a b) : ℝ :=
  let p := z.1
  let q := z.2.1
  let k := z.2.2.1
  let ell := z.2.2.2
  if (∀ i, p i ∈ P) ∧ (∀ j, q j ∈ P) ∧
      (∀ i, 1 ≤ k i) ∧ (∀ j, 1 ≤ ell j) ∧
      Finset.prod Finset.univ (fun i => p i ^ k i) =
        Finset.prod Finset.univ (fun j => q j ^ ell j)
    then
      (Finset.prod Finset.univ (fun i => Real.log (p i)) *
          Finset.prod Finset.univ (fun j => Real.log (q j))) /
        Finset.prod Finset.univ (fun i => (p i : ℝ) ^ k i)
    else 0

def collisionSum (P : Finset ℕ) (a b : ℕ) : ℝ :=
  tsum (collisionTerm P a b)

def collisionAbsolutelySummable (P : Finset ℕ) (a b : ℕ) : Prop :=
  Summable (fun z : collisionIndex a b => ‖collisionTerm P a b z‖)

def mixedCesaroAverage (P : Finset ℕ) (a b : ℕ) (T : ℝ) : ℂ :=
  T⁻¹ * ∫ t in (0 : ℝ)..T,
    (finitePrimeSeries P t) ^ a * star (finitePrimeSeries P t) ^ b

def primeMomentLowerBound (P : Finset ℕ) (a b : ℕ) : ℝ :=
  Finset.sum P (fun p =>
    (Real.log (p : ℝ)) ^ (a + b) / (p : ℝ) ^ (a * b))

def primeMomentMass (P : Finset ℕ) : ℝ :=
  Finset.sum P (fun p =>
    Real.log (p : ℝ) / (Real.sqrt (p : ℝ) - 1))

def claim59810 : Prop :=
  ∀ P : Finset ℕ,
    P.Nonempty →
    (∀ p ∈ P, Nat.Prime p) →
    (∀ p ∈ P, ∀ t : ℝ,
      Summable (fun k : ℕ => ‖primeSeriesTerm p t k‖)) ∧
    (∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
      collisionAbsolutelySummable P a b ∧
      Tendsto (mixedCesaroAverage P a b) atTop
        (𝓝 (collisionSum P a b : ℂ)) ∧
      0 < collisionSum P a b ∧
      primeMomentLowerBound P a b ≤ collisionSum P a b ∧
      collisionSum P a b ≤ primeMomentMass P ^ (a + b)) ∧
    (∀ m : ℕ, 1 ≤ m →
      collisionSum P m 1 =
        Finset.sum P (fun p =>
          (Real.log (p : ℝ)) ^ (m + 1) /
            ((p : ℝ) - 1) ^ m))


def ColoringVariable (m : ℕ) :=
  Fin (m + 1) ⊕ (Fin (m + 1) ⊕ (Fin (m + 1) × Fin (m + 1)))

def xVariable (m : ℕ) (i : Fin (m + 1)) : ColoringVariable m :=
  Sum.inl i

def zVariable (m : ℕ) (i : Fin (m + 1)) : ColoringVariable m :=
  Sum.inr (Sum.inl i)

def qVariable (m : ℕ) (i j : Fin (m + 1)) : ColoringVariable m :=
  Sum.inr (Sum.inr (if i < j then (i, j) else (j, i)))

def coloringEdgeWeight (m : ℕ) (i j : Fin (m + 1)) :
    MvPolynomial (ColoringVariable m) ℕ :=
  if i = j then MvPolynomial.X (zVariable m i)
  else MvPolynomial.X (qVariable m i j)

def edgePairs {n : ℕ} (T : SimpleGraph (Fin n)) :
    Finset (Fin n × Fin n) := by
  classical
  exact Finset.filter
    (fun e : Fin n × Fin n => e.1 < e.2 ∧ T.Adj e.1 e.2)
    Finset.univ

def fixedDegreeInvariant (m n : ℕ) (T : SimpleGraph (Fin n)) :
    MvPolynomial (ColoringVariable m) ℕ :=
  Finset.sum (Finset.univ : Finset (Fin n → Fin (m + 1))) (fun τ =>
    Finset.prod (Finset.univ : Finset (Fin n)) (fun v =>
        MvPolynomial.X (xVariable m (τ v))) *
      Finset.prod (edgePairs T) (fun e =>
        coloringEdgeWeight m (τ e.1) (τ e.2)))

def betweenEdgeCount {n : ℕ} (T : SimpleGraph (Fin n))
    (A B : Finset (Fin n)) : ℕ :=
  ((edgePairs T).filter (fun e =>
    (e.1 ∈ A ∧ e.2 ∈ B) ∨ (e.1 ∈ B ∧ e.2 ∈ A))).card

def boundaryEdgeCount {n : ℕ} (T : SimpleGraph (Fin n))
    (A : Finset (Fin n)) : ℕ :=
  ((edgePairs T).filter (fun e =>
    (e.1 ∈ A ∧ e.2 ∉ A) ∨ (e.1 ∉ A ∧ e.2 ∈ A))).card

def adjacentPairProfile {n : ℕ} (T : SimpleGraph (Fin n))
    (k l b d : ℕ) : ℕ := by
  classical
  exact (((Finset.univ : Finset (Finset (Fin n))).product
      (Finset.univ : Finset (Finset (Fin n)))).filter
      (fun AB : Finset (Fin n) × Finset (Fin n) =>
    let A : Finset (Fin n) := AB.1
    let B : Finset (Fin n) := AB.2
    Disjoint A B ∧
      A.card = k ∧ B.card = l ∧
      (SimpleGraph.induce (A : Set (Fin n)) T).Connected ∧
      (SimpleGraph.induce (B : Set (Fin n)) T).Connected ∧
      betweenEdgeCount T A B = 1 ∧
      boundaryEdgeCount T A = b ∧
      boundaryEdgeCount T B = d)).card

def colorZero (m : ℕ) : Fin (m + 1) :=
  ⟨0, by omega⟩

def colorOne (m : ℕ) (hm : 2 ≤ m) : Fin (m + 1) :=
  ⟨1, by omega⟩

def colorTwo (m : ℕ) (hm : 2 ≤ m) : Fin (m + 1) :=
  ⟨2, by omega⟩

def profileMonomial (m n k l b d : ℕ) (hm : 2 ≤ m) :
    ColoringVariable m →₀ ℕ :=
  Finsupp.single (xVariable m (colorZero m)) (n - k - l) +
  Finsupp.single (xVariable m (colorOne m hm)) k +
  Finsupp.single (xVariable m (colorTwo m hm)) l +
  Finsupp.single (zVariable m (colorOne m hm)) (k - 1) +
  Finsupp.single (zVariable m (colorTwo m hm)) (l - 1) +
  Finsupp.single (qVariable m (colorOne m hm) (colorTwo m hm)) 1 +
  Finsupp.single (qVariable m (colorZero m) (colorOne m hm)) (b - 1) +
  Finsupp.single (qVariable m (colorZero m) (colorTwo m hm)) (d - 1) +
  Finsupp.single (zVariable m (colorZero m))
    (Int.toNat ((n : ℤ) - (k : ℤ) - (l : ℤ) - (b : ℤ) - (d : ℤ) + 2))

def profileIndexCondition (n k l b d : ℕ) : Prop :=
  1 ≤ k ∧ 1 ≤ l ∧ 1 ≤ b ∧ 1 ≤ d ∧
  k + l ≤ n ∧
  0 ≤ (n : ℤ) - (k : ℤ) - (l : ℤ) - (b : ℤ) - (d : ℤ) + 2

def claim59812 : Prop :=
  ∀ (m n : ℕ) (T : SimpleGraph (Fin n)),
    ∀ (hm : 2 ≤ m) (hn : 2 ≤ n) (hT : T.IsTree),
    (∀ k l b d : ℕ, profileIndexCondition n k l b d →
      adjacentPairProfile T k l b d =
        MvPolynomial.coeff
          (profileMonomial m n k l b d hm)
          (fixedDegreeInvariant m n T)) ∧
    (∀ T' : SimpleGraph (Fin n), T'.IsTree →
      (fixedDegreeInvariant m n T = fixedDegreeInvariant m n T' →
        ∀ k l b d : ℕ, profileIndexCondition n k l b d →
          adjacentPairProfile T k l b d = adjacentPairProfile T' k l b d) ∧
      ((∃ k l b d : ℕ,
          profileIndexCondition n k l b d ∧
            adjacentPairProfile T k l b d ≠ adjacentPairProfile T' k l b d) →
        ∀ m' : ℕ, 2 ≤ m' →
          fixedDegreeInvariant m' n T ≠ fixedDegreeInvariant m' n T'))

end
end MathlibPlus.Open.ResearchFormalization
