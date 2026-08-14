import Mathlib

noncomputable section

namespace MathlibPlus.Open.ResearchFormalizationBatch_01a000fa

/-! The algebraic core of R-3566.1.  The packet explicitly identifies this
    derivative obstruction as equivalent to the central-return obstruction. -/
namespace SignedCopy

/-- The Littlewood polynomial with coefficients indexed as in the packet. -/
def littlewoodPolynomial (m : ℕ) (a : Fin m → ℤ) : Polynomial ℤ :=
  ∑ r : Fin m, Polynomial.C (a r) * Polynomial.X ^ (m - r.1 - 1)

/-- Every coefficient is one of the two allowed Littlewood signs. -/
def IsLittlewood (m : ℕ) (a : Fin m → ℤ) : Prop :=
  ∀ r, a r = (-1 : ℤ) ∨ a r = (1 : ℤ)

/-- The quantity which the claimed new-return condition would require to
    vanish. -/
def derivativeExpression (h m : ℕ) (a : Fin m → ℤ) : ℤ :=
  let y : ℤ := 2 ^ h
  (m : ℤ) * (littlewoodPolynomial m a).eval y
    - y * (littlewoodPolynomial m a).derivative.eval y

/-- Signed-copy substitution cannot satisfy the central-return derivative
    condition for any h ≥ 2 and any nonempty Littlewood block. -/
def signedCopyDerivativeObstruction : Prop :=
  ∀ (h m : ℕ), 2 ≤ h → 1 ≤ m →
    ∀ a : Fin m → ℤ, IsLittlewood m a →
      derivativeExpression h m a ≠ 0

end SignedCopy

/-! R-3568.1--R-3568.2: the explicitly displayed four-bit components and
    their exact two-point mixture.  Bool records the packet's false/true
    encoding of the signs -1/+1. -/
namespace DepthTwoMixture

/-- The queried coordinates, in order, for the first displayed tree. -/
def h₁Path (x : Fin 4 → Bool) : List (Fin 4) :=
  [1, if x 1 then 3 else 0]

/-- The queried coordinates, in order, for the second displayed tree. -/
def h₂Path (x : Fin 4 → Bool) : List (Fin 4) :=
  [2, if x 2 then 3 else 0]

/-- A displayed path has the claimed exact cost and no repeated coordinate. -/
def exactDepthTwoPath (path : List (Fin 4)) : Prop :=
  path.length = 2 ∧ path.Nodup

/-- Statement S1: both displayed trees have two distinct queries on every
    completion, with the branch choices given in the packet. -/
def twoDepthTwoComponentTrees : Prop :=
  ∀ x : Fin 4 → Bool,
    exactDepthTwoPath (h₁Path x) ∧ exactDepthTwoPath (h₂Path x)

/-- The two nonzero mixture weights from Statement S2. -/
def mixtureWeight (j : Fin 2) : ℚ :=
  if j = 0 then (25 : ℚ) / 27 else (2 : ℚ) / 27

/-- The mixture has exactly the two displayed components. -/
def mixtureComponent (j : Fin 2) (x : Fin 4 → Bool) : List (Fin 4) :=
  if j = 0 then h₁Path x else h₂Path x

/-- Statement S2: the support consists of H₁ and H₂, with the stated weights,
    and each component has expected (indeed pointwise) cost two. -/
def exactDepthTwoMixture : Prop :=
  h₁Path ≠ h₂Path ∧
  mixtureWeight 0 = (25 : ℚ) / 27 ∧
  mixtureWeight 1 = (2 : ℚ) / 27 ∧
  (∑ j : Fin 2, mixtureWeight j) = 1 ∧
  ∀ j : Fin 2, mixtureWeight j > 0 ∧
    ∀ x : Fin 4 → Bool, (mixtureComponent j x).length = 2

end DepthTwoMixture

/-! R-3691: a concrete block-labelled realization of the recursive selector
    construction.  The offsets make the two recursive copies disjoint and
    put them after the root in the stated coordinate order. -/
namespace SelectorConstruction

inductive SelectorTree where
  | leaf : ℕ → SelectorTree
  | branch : ℕ → SelectorTree → SelectorTree → SelectorTree

/-- Number of coordinate-labelled nodes. -/
def treeSize : SelectorTree → ℕ
  | .leaf _ => 1
  | .branch _ left right => 1 + treeSize left + treeSize right

/-- Add an offset to every coordinate label. -/
def relabel (offset : ℕ) : SelectorTree → SelectorTree
  | .leaf coordinate => .leaf (offset + coordinate)
  | .branch coordinate left right =>
      .branch (offset + coordinate) (relabel offset left) (relabel offset right)

/-- The set of coordinates used by a selector tree. -/
def coordinates : SelectorTree → Finset ℕ
  | .leaf coordinate => {coordinate}
  | .branch coordinate left right =>
      insert coordinate (coordinates left ∪ coordinates right)

/-- H₀ is a one-coordinate leaf; each later level has a fresh root and two
    disjoint, consecutively placed copies of the preceding level. -/
def selectorTree : ℕ → SelectorTree
  | 0 => .leaf 0
  | level + 1 =>
      let previous := selectorTree level
      .branch 0 (relabel 1 previous)
        (relabel (1 + treeSize previous) previous)

/-- Statement 48053: the recursively constructed H₃ uses precisely fifteen
    coordinates in root/left-subtree/right-subtree block order. -/
def hThreeUsesFifteenCoordinates : Prop :=
  treeSize (selectorTree 3) = 15 ∧
    coordinates (selectorTree 3) = Finset.range 15

end SelectorConstruction

/-! R-3692: the centered Euler-pair identity and its explicit reciprocal
    polynomial/root data. -/
namespace CenteredEulerPair

/-- The inverse square-root quantity appearing in the packet. -/
def inverseSqrt (p : ℕ) : ℝ :=
  Real.rpow (p : ℝ) (-((1 : ℝ) / 2))

/-- X = p^q in the centered coordinate. -/
def centeredVariable (p : ℕ) (q : ℝ) : ℝ :=
  Real.rpow (p : ℝ) q

/-- E_p(q) = (1-p^(-s))(1-p^(s-1)), with s=1/2+q. -/
def centeredEulerPair (p : ℕ) (q : ℝ) : ℝ :=
  let s : ℝ := (1 : ℝ) / 2 + q
  (1 - Real.rpow (p : ℝ) (-s)) * (1 - Real.rpow (p : ℝ) (s - 1))

/-- The reciprocal polynomial in the packet. -/
def reciprocalPolynomial (p : ℕ) : Polynomial ℝ :=
  Polynomial.X ^ 2
    - Polynomial.C (Real.sqrt (p : ℝ) + inverseSqrt p) * Polynomial.X
    + 1

/-- The full identity and unequal-root-modulus assertion of Claim 48076. -/
def centeredEulerPairClaim : Prop :=
  ∀ p : ℕ, Nat.Prime p →
    (∀ q : ℝ,
      -(p : ℝ) * centeredEulerPair p q =
        Real.sqrt (p : ℝ) *
          (centeredVariable p q + (centeredVariable p q)⁻¹
            - Real.sqrt (p : ℝ) - inverseSqrt p)) ∧
    reciprocalPolynomial p =
      (Polynomial.X - Polynomial.C (Real.sqrt (p : ℝ))) *
        (Polynomial.X - Polynomial.C (inverseSqrt p)) ∧
    |Real.sqrt (p : ℝ)| ≠ |inverseSqrt p|

end CenteredEulerPair

/-! R-3692.2: the added rank-two encoding is represented by its concrete
    two-dimensional complex matrix and positive Hermitian Gram form. -/
namespace PositiveGramEncoding

/-- A positive Hermitian Gram matrix on the concrete two-dimensional complex
    space. -/
def positiveGram (G : Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  (∀ i j, G i j = star (G j i)) ∧
    ∀ v : Fin 2 → ℂ, v ≠ 0 →
      0 < (∑ i : Fin 2, ∑ j : Fin 2,
        star (v i) * G i j * v j).re

/-- Multiplication by the Laurent variable preserves the Gram form. -/
def preservesGram (A G : Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  ∀ v w : Fin 2 → ℂ,
    (∑ i : Fin 2, ∑ j : Fin 2,
      star (v i) * G i j * w j) =
    (∑ i : Fin 2, ∑ j : Fin 2,
      star ((A.mulVec v) i) * G i j * (A.mulVec w) j)

/-- No prime centered Euler polynomial can be the characteristic polynomial
    of a Gram-unitary rank-two encoding. -/
def noPositiveGramPrimeEncoding : Prop :=
  ∀ p : ℕ, Nat.Prime p →
    ¬ ∃ A G : Matrix (Fin 2) (Fin 2) ℂ,
      positiveGram G ∧ preservesGram A G ∧
        Matrix.charpoly A =
          (Polynomial.X - Polynomial.C (Real.sqrt (p : ℝ) : ℂ)) *
            (Polynomial.X -
              Polynomial.C (CenteredEulerPair.inverseSqrt p : ℂ))

end PositiveGramEncoding

end MathlibPlus.Open.ResearchFormalizationBatch_01a000fa
