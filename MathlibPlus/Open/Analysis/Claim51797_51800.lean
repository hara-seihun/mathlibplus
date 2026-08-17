import MathlibPlus.Open.Analysis.GammaReadout

noncomputable section

namespace MathlibPlus.Open.Analysis

open MeasureTheory
open scoped BigOperators

/-- The shape and the row parameter used by the folded Gamma packet. -/
def claim51797Shape : ℝ := 5 / 4

def claim51797Q (x : ℝ) : ℝ :=
  Real.pi * x ^ 2

def claim51797H (q u : ℝ) : ℝ :=
  Real.exp (-2 * claim51797Shape * u - q * Real.exp (-2 * u)) +
    Real.exp (2 * claim51797Shape * u - q * Real.exp (2 * u))

def claim51797Rho (x u : ℝ) : ℝ :=
  2 * Real.rpow (claim51797Q x) claim51797Shape /
      Real.Gamma claim51797Shape * claim51797H (claim51797Q x) u

def claim51797MinusSheet (x u : ℝ) : ℝ :=
  claim51797Q x * Real.exp (-2 * u)

def claim51797PlusSheet (x u : ℝ) : ℝ :=
  claim51797Q x * Real.exp (2 * u)

/-- The density obtained from the two Gamma changes of variables. -/
def claim51797SheetDensity (x u : ℝ) : ℝ :=
  2 * (gammaDensity (claim51797MinusSheet x u) *
        claim51797MinusSheet x u +
      gammaDensity (claim51797PlusSheet x u) *
        claim51797PlusSheet x u)

/-- `P_j(y) = E[(y+Z)^(2j)]` for
`Z = (1/2) log (pi/T)` and `T` having the displayed Gamma law. -/
def claim51797P (j : ℕ) (y : ℝ) : ℝ :=
  gammaExpectation (fun t =>
    (y + (1 / 2 : ℝ) * Real.log (Real.pi / t)) ^ (2 * j))

def claim51797SheetMoment (x : ℝ) (j : ℕ) : ℝ :=
  ∫ u in Set.Ioi (0 : ℝ),
    u ^ (2 * j) * claim51797SheetDensity x u

def claim51797FoldedMoment (x : ℝ) (j : ℕ) : ℝ :=
  ∫ u in Set.Ioi (0 : ℝ),
    u ^ (2 * j) * claim51797Rho x u

/-- Claim 51797: the two sheets of the Gamma fold give the positive folded
 density and the shifted even-moment representation. -/
def claim51797 : Prop :=
  ∀ x : ℝ, 0 < x →
    (∀ u : ℝ, 0 < u →
      claim51797SheetDensity x u = claim51797Rho x u) ∧
    (∀ u : ℝ, 0 < u → 0 < claim51797Rho x u) ∧
    (∀ j : ℕ,
      claim51797P j (Real.log x) = claim51797FoldedMoment x j) ∧
    (∀ j : ℕ,
      claim51797P j (Real.log x) = claim51797SheetMoment x j)

def claim51800ProductMeasure (r : ℕ) : Measure (Fin r → ℝ) :=
  Measure.pi (fun _ : Fin r =>
    Measure.restrict volume (Set.Ioi (0 : ℝ)))

def claim51800MomentDet (r : ℕ) (j : Fin r → ℕ)
    (x : Fin r → ℝ) : ℝ :=
  Matrix.det (fun i k => claim51797P (j k) (Real.log (x i)))

def claim51800FoldedDet (r : ℕ) (x : Fin r → ℝ)
    (u : Fin r → ℝ) : ℝ :=
  Matrix.det (fun i l => claim51797Rho (x i) (u l))

def claim51800MonomialDet (r : ℕ) (j : Fin r → ℕ)
    (u : Fin r → ℝ) : ℝ :=
  Matrix.det (fun l k => (u l) ^ (2 * j k))

/-- Claim 51800: Andreief's determinant readout uses the folded-kernel
 determinant, and the even-monomial factor is positive on the ordered
 positive simplex. -/
def claim51800 : Prop :=
  (∀ (r : ℕ) (j : Fin r → ℕ) (x : Fin r → ℝ),
    StrictMono j →
    (∀ i, 0 < x i) →
    claim51800MomentDet r j x =
      (1 / (Nat.factorial r : ℝ)) *
        ∫ u : Fin r → ℝ,
          claim51800FoldedDet r x u * claim51800MonomialDet r j u
            ∂claim51800ProductMeasure r) ∧
  (∀ (r : ℕ) (j : Fin r → ℕ) (u : Fin r → ℝ),
    StrictMono j → StrictMono u → (∀ l, 0 < u l) →
      0 < claim51800MonomialDet r j u)

end MathlibPlus.Open.Analysis
