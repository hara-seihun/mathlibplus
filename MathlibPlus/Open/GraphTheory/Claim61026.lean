import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.GraphTheory.Claim61026

noncomputable section

abbrev F7 := ZMod 7
abbrev Base := Fin 4 → F7
abbrev Coefficient := Fin 5 → F7
abbrev PotentialPolynomial := Fin 5 → MvPolynomial (Fin 4) F7

/-- The nine directions in the displayed rank-nine profile. -/
def directions : Fin 9 → Base :=
  ![![1, 0, 0, 0],
    ![0, 1, 0, 0],
    ![0, 0, 1, 0],
    ![0, 0, 0, 1],
    ![5, 5, 3, 0],
    ![2, 1, 3, 6],
    ![4, 1, 3, 5],
    ![4, 4, 2, 6],
    ![5, 4, 2, 4]]

/-- The nine coefficient covectors in the displayed rank-nine profile. -/
def covectors : Fin 9 → Coefficient :=
  ![![2, 5, 3, 3, 2],
    ![2, 6, 6, 3, 3],
    ![4, 4, 4, 5, 5],
    ![0, 1, 2, 1, 3],
    ![1, 0, 0, 0, 0],
    ![0, 1, 0, 0, 0],
    ![0, 0, 1, 0, 0],
    ![0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 1]]

/-- The coefficient pairing used by each displayed covector. -/
def coefficientPairing (u a : Coefficient) : F7 :=
  ∑ j : Fin 5, u j * a j

/-- A monomial has one of the four retained odd total degrees and is reduced
in every variable over `F_7`. -/
def retainedMonomial (m : Fin 4 →₀ ℕ) : Prop :=
  (∀ j : Fin 4, m j < 7) ∧
    (m.sum (fun _ e => e) = 1 ∨
      m.sum (fun _ e => e) = 3 ∨
      m.sum (fun _ e => e) = 5 ∨
      m.sum (fun _ e => e) = 7)

/-- Coordinate polynomials representing the complete reduced odd potential
space of total degree at most seven. -/
def isRetainedPotential (p : PotentialPolynomial) : Prop :=
  ∀ a : Fin 5, ∀ m ∈ (p a).support, retainedMonomial m

/-- Evaluation of a coordinate-polynomial potential on the base space. -/
def evaluatePotential (p : PotentialPolynomial) (x : Base) : Coefficient :=
  fun a => MvPolynomial.eval x (p a)

/-- The normalized finite-difference equations for the nine rows. -/
def profileDifferenceEquation (p : PotentialPolynomial)
    (lambda : Fin 9 → F7) : Prop :=
  ∀ (i : Fin 9) (x : Base),
    coefficientPairing (covectors i)
        (evaluatePotential p (x + directions i) - evaluatePotential p x) = lambda i

/-- The exact no-coefficient-hyperplane theorem for the displayed `F_7` profile. -/
def rankNineNoCoefficientHyperplane : Prop :=
  ∀ (p : PotentialPolynomial) (lambda : Fin 9 → F7),
    isRetainedPotential p →
      profileDifferenceEquation p lambda →
        (∑ i : Fin 9, lambda i ≠ 0) →
          Submodule.span F7 (Set.range (evaluatePotential p)) = ⊤ ∧
            (∀ w : Coefficient →ₗ[F7] F7,
              w ≠ 0 →
                ∃ x : Base, w (evaluatePotential p x) ≠ 0)

end

end MathlibPlus.Open.GraphTheory.Claim61026
