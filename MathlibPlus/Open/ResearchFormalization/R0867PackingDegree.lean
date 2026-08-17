import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0867PackingDegree

noncomputable section

abbrev Form (σ : Type*) := MvPolynomial σ (RatFunc ℚ)

def scalarForm {σ : Type*} (q : ℚ) : Form σ :=
  MvPolynomial.C (algebraMap ℚ (RatFunc ℚ) q)

def centeredA {σ : Type*} (K : Fin 4 → Form σ) : Form σ := K 0 - K 2
def centeredB {σ : Type*} (K : Fin 4 → Form σ) : Form σ := K 1 - K 2
def centeredD {σ : Type*} (K : Fin 4 → Form σ) : Form σ := K 3 - K 2

/-- Four distinct homogeneous coefficient forms of one common z-degree in
`Q(x)[z]`; the variable type is left arbitrary rather than imposing an
extra binary or total-degree presentation. -/
def homogeneousAllDistinctCrossRatio {σ : Type*} [DecidableEq σ]
    (K : Fin 4 → Form σ) (lam : ℚ) (h : ℕ) : Prop :=
  (∀ i : Fin 4, K i ≠ 0 ∧ MvPolynomial.IsHomogeneous (K i) h) ∧
    (∀ ⦃i j : Fin 4⦄, i ≠ j → K i ≠ K j) ∧
    lam ≠ 0 ∧ lam ≠ 1 ∧
    (K 0 - K 3) * (K 1 - K 2) =
      scalarForm lam * (K 0 - K 2) * (K 1 - K 3)

/-- The four displayed forms lie on one affine line in the form space. -/
def affineFormLine {σ : Type*}
    (K : Fin 4 → Form σ) : Prop :=
  ∃ P H : Form σ, H ≠ 0 ∧
    ∃ coefficients : Fin 4 → RatFunc ℚ,
      ∀ i : Fin 4, K i = P + MvPolynomial.C (coefficients i) * H

/-- The primitive common-context binary factor rectangle. -/
def primitiveBinaryPairRectangle {σ : Type*} [DecidableEq σ]
    (K : Fin 4 → Form σ) (lam : ℚ) : Prop :=
  ∃ H X Y : Form σ,
    H ≠ 0 ∧
    MvPolynomial.IsHomogeneous H 0 ∧
    MvPolynomial.IsHomogeneous X 1 ∧
    MvPolynomial.IsHomogeneous Y 1 ∧
    IsCoprime X Y ∧
    IsCoprime (scalarForm lam * X - Y) X ∧
    IsCoprime (scalarForm lam * X - Y) Y ∧
    centeredA K = H * (scalarForm lam * X - Y) * X ∧
    centeredB K = H * (scalarForm lam * X - Y) * Y ∧
    centeredD K = scalarForm (lam - 1) * H * X * Y

/-- Claim 25478: packing degree one forces the affine-line case; at degree two,
 every non-line solution has constant homogeneous context and homogeneous
 linear primitive directions. -/
def claim25478 : Prop :=
  ∀ (σ : Type*) [DecidableEq σ]
    (K : Fin 4 → Form σ) (lam : ℚ) (h : ℕ),
    homogeneousAllDistinctCrossRatio K lam h →
      ((h = 1 → affineFormLine K) ∧
        (h = 2 → ¬affineFormLine K →
          primitiveBinaryPairRectangle K lam))

end
end MathlibPlus.Open.ResearchFormalization.R0867PackingDegree
