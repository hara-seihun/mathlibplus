import Mathlib
import MathlibPlus.Algebra.Claim41526
import MathlibPlus.Open.ResearchFormalization.R0849

open scoped BigOperators

noncomputable section
open Classical

namespace MathlibPlus.Open.ResearchFormalization.R1166.Claim31763

abbrev MarkerRing := MvPolynomial ℕ ℚ
abbrev StrictLowerRing (J : ℕ) := MvPolynomial (Fin (J - 1)) ℚ

/-- The finite-variable labels for `t,c₂,…,c_(J-1)`. -/
def strictLowerIndex (J : ℕ) (i : Fin (J - 1)) : ℕ :=
  if i.val = 0 then 0 else i.val + 1

/-- The finite strict-lower-marker presentation embedded in the full marker
polynomial ring. -/
noncomputable def strictLowerEmbedding (J : ℕ) :
    StrictLowerRing J →ₐ[ℚ] MarkerRing :=
  MvPolynomial.rename (strictLowerIndex J)

/-- A connected set deleted from a finite graph in the terminal transform. -/
def connectedDeletedBlock {V : Type*} [DecidableEq V]
    (X : SimpleGraph V) (A : Finset V) : Prop :=
  A.Nonempty ∧ (X.induce (A : Set V)).Connected

/-- The terminal forest remaining after deletion of a connected block. -/
def deletedForest {V : Type*} [DecidableEq V]
    (X : SimpleGraph V) (A : Finset V) :
    SimpleGraph {v : V // v ∉ (A : Set V)} :=
  X.induce {v : V | v ∉ (A : Set V)}

/-- The packing polynomial of a finite terminal forest. -/
noncomputable def forestPackingPolynomial {V : Type*} [Fintype V]
    [DecidableEq V] (F : SimpleGraph V) : MarkerRing :=
  ∑ k ∈ Finset.range (Fintype.card V + 1),
    MathlibPlus.Open.ResearchFormalization.R0849.connectedPackingCoefficient F k

/-- The exact sum of packing polynomials over connected deletions of order
`m - r`. -/
noncomputable def terminalComplementTransform {V : Type*} [Fintype V]
    [DecidableEq V] (X : SimpleGraph V) (m r : ℕ) : MarkerRing :=
  ∑ A ∈ (Finset.univ : Finset (Finset V)).filter
      (fun A => A.card = m - r ∧ connectedDeletedBlock X A),
    forestPackingPolynomial (deletedForest X A)

/-- Equality of the three terminal transforms at one complement order. -/
def terminalTransformsAgree {V : Type*} [Fintype V] [DecidableEq V]
    (S T R : SimpleGraph V) (m r : ℕ) : Prop :=
  terminalComplementTransform S m r = terminalComplementTransform T m r ∧
    terminalComplementTransform R m r = terminalComplementTransform T m r

/-- The least complement order at which the three terminal transforms differ. -/
def firstDifferingTerminalOrder {V : Type*} [Fintype V]
    [DecidableEq V] (S T R : SimpleGraph V) (m r : ℕ) : Prop :=
  (∀ q : ℕ, q < r → terminalTransformsAgree S T R m q) ∧
    ¬terminalTransformsAgree S T R m r

/-- The strict lower-marker carrier `R_<J`. -/
def strictLowerMarker (J : ℕ) (P : MarkerRing) : Prop :=
  MvPolynomial.degreeOf 1 P = 0 ∧
    ∀ K : ℕ, J ≤ K → MvPolynomial.degreeOf K P = 0

/-- A primitive linear prime with largest marker `J`. -/
def primitiveLinearPrime (J : ℕ) (p : MarkerRing) : Prop :=
  Prime p ∧
    0 < MvPolynomial.degreeOf J p ∧
      (∀ K : ℕ, J < K → MvPolynomial.degreeOf K p = 0) ∧
        ∃ a b : StrictLowerRing J,
          a ≠ 0 ∧
            strictLowerMarker J ((strictLowerEmbedding J) a) ∧
              strictLowerMarker J ((strictLowerEmbedding J) b) ∧
                p = (strictLowerEmbedding J) a * MvPolynomial.X J +
                  (strictLowerEmbedding J) b

/-- The affine line through `T` in the direction of the common prime, with
rational parameters. -/
def rationalAffineTerminalLine
    (thetaT thetaS thetaR p : MarkerRing) : Prop :=
  ∃ qS qR : ℚ,
    thetaS - thetaT = MvPolynomial.C qS * p ∧
      thetaR - thetaT = MvPolynomial.C qR * p

/-- The repeated-transform alternative. -/
def repeatedTerminalTransform
    (thetaT thetaS thetaR : MarkerRing) : Prop :=
  thetaS = thetaT ∨ thetaR = thetaT

/-- The exact common-prime, quotient, and strict-lower-marker data preceding
Claim 31763. -/
def terminalUnitQuotientContext {V : Type*} [Fintype V]
    [DecidableEq V]
    (S T R : SimpleGraph V) (m r J : ℕ)
    (p : MarkerRing) (hS hR : StrictLowerRing J) : Prop :=
  2 ≤ J ∧
    J ≤ m / 2 ∧
      J ≤ r ∧
        r < 2 * J ∧
          Fintype.card V = m ∧
            firstDifferingTerminalOrder S T R m r ∧
        primitiveLinearPrime J p ∧
          p ∣ terminalComplementTransform S m r -
            terminalComplementTransform T m r ∧
            p ∣ terminalComplementTransform R m r -
              terminalComplementTransform T m r ∧
              terminalComplementTransform S m r -
                  terminalComplementTransform T m r =
                (strictLowerEmbedding J) hS * p ∧
                terminalComplementTransform R m r -
                    terminalComplementTransform T m r =
                  (strictLowerEmbedding J) hR * p ∧
                  strictLowerMarker J ((strictLowerEmbedding J) hS) ∧
                    strictLowerMarker J ((strictLowerEmbedding J) hR)

/-- Claim 31763: zero quotients give the repeated-transform exit, while two
nonzero unit quotients force the three exact terminal transforms onto a
rational affine line. -/
def claim31763 : Prop :=
  ∀ {V : Type*} [Fintype V] [DecidableEq V]
    (S T R : SimpleGraph V) (m r J : ℕ)
    (p : MarkerRing) (hS hR : StrictLowerRing J),
    terminalUnitQuotientContext S T R m r J p hS hR →
      ((hS = 0 ∨ hR = 0) ∨
        (hS ≠ 0 ∧ hR ≠ 0 ∧ IsUnit hS ∧ IsUnit hR)) →
      (((hS = 0 ∨ hR = 0) ∧
          repeatedTerminalTransform
            (terminalComplementTransform T m r)
            (terminalComplementTransform S m r)
            (terminalComplementTransform R m r)) ∨
        (hS ≠ 0 ∧ hR ≠ 0 ∧ IsUnit hS ∧ IsUnit hR ∧
          rationalAffineTerminalLine
            (terminalComplementTransform T m r)
            (terminalComplementTransform S m r)
            (terminalComplementTransform R m r) p))

end MathlibPlus.Open.ResearchFormalization.R1166.Claim31763
