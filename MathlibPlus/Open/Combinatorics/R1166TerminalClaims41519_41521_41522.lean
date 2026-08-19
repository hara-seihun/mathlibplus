import Mathlib
import MathlibPlus.Open.ResearchFormalization.R0849

open scoped BigOperators

namespace MathlibPlus.Open.Combinatorics.R1166

noncomputable section
open Classical

abbrev MarkerRing := MvPolynomial ℕ ℚ

/-- A connected deleted block in a finite graph. -/
def connectedDeletedBlock {V : Type*} [DecidableEq V]
    (X : SimpleGraph V) (A : Finset V) : Prop :=
  A.Nonempty ∧ (X.induce (A : Set V)).Connected

/-- The forest left after deleting the connected block `A`. -/
def deletedForest {V : Type*} [DecidableEq V]
    (X : SimpleGraph V) (A : Finset V) :
    SimpleGraph {v : V // v ∉ (A : Set V)} :=
  X.induce {v : V | v ∉ (A : Set V)}

/-- The complete packing polynomial of a finite forest.  Variable `0` is the
singleton marker `t`; variable `k` is the marker `c_k` for a selected
connected component of order `k`. -/
noncomputable def forestPackingPolynomial {V : Type*} [Fintype V]
    [DecidableEq V] (F : SimpleGraph V) : MarkerRing :=
  ∑ r ∈ Finset.range (Fintype.card V + 1),
    MathlibPlus.Open.ResearchFormalization.R0849.connectedPackingCoefficient F r

/-- The exact terminal transform: sum the packing polynomials of the forests
obtained by deleting one connected set of order `m-r`. -/
noncomputable def terminalComplementTransform {V : Type*} [Fintype V]
    [DecidableEq V] (X : SimpleGraph V) (m r : ℕ) : MarkerRing :=
  ∑ A ∈ (Finset.univ : Finset (Finset V)).filter
      (fun A => A.card = m - r ∧ connectedDeletedBlock X A),
    forestPackingPolynomial (deletedForest X A)

/-- The three terminal transforms agree at order `q`. -/
def terminalTransformsAgree {V : Type*} [Fintype V] [DecidableEq V]
    (S T R : SimpleGraph V) (m q : ℕ) : Prop :=
  terminalComplementTransform S m q = terminalComplementTransform T m q ∧
    terminalComplementTransform R m q = terminalComplementTransform T m q

/-- `r` is the least complement order below the upper half at which the three
terminal transforms do not all agree. -/
def firstDifferingTerminalOrder {V : Type*} [Fintype V]
    [DecidableEq V] (S T R : SimpleGraph V) (m r : ℕ) : Prop :=
  r < m / 2 ∧
    (∀ q : ℕ, q < r → terminalTransformsAgree S T R m q) ∧
    ¬terminalTransformsAgree S T R m r

/-- Exact active-tree U-polynomial carrier used for the common lower-half
factor.  The active polynomial is the complete packing polynomial of the
connected tree itself. -/
noncomputable def activePolynomial {V : Type*} [Fintype V]
    [DecidableEq V] (X : SimpleGraph V) : MarkerRing :=
  forestPackingPolynomial X

/-- A normalized active difference is the quotient after removing the
universal singleton factor `t`.  The existential quotient keeps the exact
polynomial divisibility semantics without choosing a quotient. -/
def normalizedActiveDifference {V : Type*} [Fintype V]
    [DecidableEq V] (S T : SimpleGraph V) (d : MarkerRing) : Prop :=
  activePolynomial S - activePolynomial T =
      MvPolynomial.X 0 * d

/-- The common lower-half irreducible prime relation.  In particular, `p` is
not merely a polynomial with largest marker `J`: it divides both normalized
active differences and is supported only in the lower half. -/
def commonLowerHalfPrime {V : Type*} [Fintype V]
    [DecidableEq V] (S T R : SimpleGraph V) (m J : ℕ) (p : MarkerRing) : Prop :=
  Prime p ∧
    2 ≤ J ∧ J ≤ m / 2 ∧
    0 < MvPolynomial.degreeOf J p ∧
    (∀ K : ℕ, J < K → MvPolynomial.degreeOf K p = 0) ∧
    (∃ dST : MarkerRing,
      normalizedActiveDifference S T dST ∧ p ∣ dST) ∧
    (∃ dRT : MarkerRing,
      normalizedActiveDifference R T dRT ∧ p ∣ dRT)

/-- Independence from the distinguished marker `c_J`. -/
def markerFreeAt (J : ℕ) (q : MarkerRing) : Prop :=
  MvPolynomial.degreeOf J q = 0

/-- The strict lower-marker ring `R_<J = ℚ[t,c₂,…,c_(J-1)}`. -/
def strictLowerMarker (J : ℕ) (q : MarkerRing) : Prop :=
  MvPolynomial.degreeOf 1 q = 0 ∧
    ∀ K : ℕ, J ≤ K → MvPolynomial.degreeOf K q = 0

/-- Claim 41519: the common lower-half prime divides both first terminal
transform differences. -/
def claim41519 : Prop :=
  ∀ {V : Type*} [Fintype V] [DecidableEq V]
    (S T R : SimpleGraph V) (m J r : ℕ) (p : MarkerRing),
    Fintype.card V = m →
    S.IsTree ∧ T.IsTree ∧ R.IsTree →
    commonLowerHalfPrime S T R m J p →
    firstDifferingTerminalOrder S T R m r →
    p ∣ terminalComplementTransform S m r -
          terminalComplementTransform T m r ∧
      p ∣ terminalComplementTransform R m r -
          terminalComplementTransform T m r

/-- Claim 41521: in the one-largest-marker band, the two first terminal
transform differences are affine-linear in `c_J`, with every coefficient
independent of `c_J`. -/
def claim41521 : Prop :=
  ∀ {V : Type*} [Fintype V] [DecidableEq V]
    (S T R : SimpleGraph V) (m J r : ℕ),
    Fintype.card V = m →
    S.IsTree ∧ T.IsTree ∧ R.IsTree →
    2 ≤ J → J ≤ r → r < 2 * J →
    firstDifferingTerminalOrder S T R m r →
    ∃ A_S B_S A_R B_R : MarkerRing,
      markerFreeAt J A_S ∧ markerFreeAt J B_S ∧
        markerFreeAt J A_R ∧ markerFreeAt J B_R ∧
        terminalComplementTransform S m r -
            terminalComplementTransform T m r =
          A_S + MvPolynomial.X J * B_S ∧
        terminalComplementTransform R m r -
            terminalComplementTransform T m r =
          A_R + MvPolynomial.X J * B_R

/-- Claim 41522: in the one-marker band, the common `c_J`-dependent
irreducible prime is primitive linear over the strict lower-marker ring. -/
def claim41522 : Prop :=
  ∀ {V : Type*} [Fintype V] [DecidableEq V]
    (S T R : SimpleGraph V) (m J r : ℕ) (p : MarkerRing),
    Fintype.card V = m →
    S.IsTree ∧ T.IsTree ∧ R.IsTree →
    commonLowerHalfPrime S T R m J p →
    J ≤ r → r < 2 * J →
    firstDifferingTerminalOrder S T R m r →
    ∃ a b : MarkerRing,
      strictLowerMarker J a ∧ strictLowerMarker J b ∧ a ≠ 0 ∧
        p = a * MvPolynomial.X J + b

end

end MathlibPlus.Open.Combinatorics.R1166
