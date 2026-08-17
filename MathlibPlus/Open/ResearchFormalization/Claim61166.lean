import Mathlib

open scoped BigOperators TensorProduct

namespace MathlibPlus.Open.ResearchFormalization.Claim61166

noncomputable section

abbrev Scalar := ZMod 23
abbrev TIndex := Fin 11
abbrev QRaw := TIndex → Scalar
abbrev QCoord := Fin 8 → Scalar
abbrev Fibre := Fin 3 → Scalar
abbrev A := QCoord →ₗ[Scalar] Scalar
abbrev V := A × Fibre
abbrev Polynomial := MvPolynomial (Fin 3) Scalar

/-- The ordered label set `T` from the retained rank-eleven construction. -/
def tValues : TIndex → Scalar :=
  ![1, 2, 3, 4, 6, 8, 9, 12, 13, 16, 18]

def qMoment (c : QRaw) : Prop :=
  (∑ j : TIndex, c j = 0) ∧
    (∑ j : TIndex, tValues j * c j = 0) ∧
      (∑ j : TIndex, (tValues j) ^ 3 * c j = 0)

/-- Coordinates on the eight-dimensional moment kernel.  The final three
coordinates are the exact solution of the three displayed moment equations. -/
def qEmbed (c : QCoord) : QRaw :=
  ![
    c 0,
    c 1,
    c 2,
    c 3,
    c 4,
    c 5,
    c 6,
    c 7,
    (3 : Scalar) * c 0 + 19 * c 1 + 2 * c 2 + 16 * c 3 +
      2 * c 4 + 6 * c 5 + 8 * c 6,
    7 * c 0 + 2 * c 1 + 22 * c 2 + 22 * c 3 +
      12 * c 4 + 3 * c 5 + 10 * c 6 + 20 * c 7,
    12 * c 0 + c 1 + 21 * c 2 + 7 * c 3 +
      8 * c 4 + 13 * c 5 + 4 * c 6 + 2 * c 7
  ]

def momentCoordinateModel : Prop :=
  Function.Injective qEmbed ∧
    ∀ c : QRaw, qMoment c ↔ ∃ u : QCoord, qEmbed u = c

def momentRowsIndependent : Prop :=
  ∀ a b c : Scalar,
    (∀ j : TIndex,
      a + b * tValues j + c * (tValues j) ^ 3 = 0) →
        a = 0 ∧ b = 0 ∧ c = 0

/-- The eleven covectors, represented in the chosen exact coordinates of the
moment kernel. -/
def cTau : TIndex → QCoord :=
  ![
    ![9, 0, 0, 17, 0, 0, 0, 0],
    ![13, 0, 0, 0, 15, 0, 0, 0],
    ![19, 0, 0, 0, 0, 0, 12, 0],
    ![0, 8, 16, 0, 0, 0, 0, 0],
    ![0, 18, 0, 0, 0, 11, 0, 0],
    ![0, 20, 0, 0, 0, 0, 10, 16],
    ![0, 0, 11, 13, 0, 0, 0, 0],
    ![0, 0, 19, 0, 0, 9, 0, 18],
    ![0, 0, 0, 16, 9, 0, 0, 0],
    ![0, 0, 0, 0, 22, 3, 21, 0],
    ![0, 0, 0, 0, 0, 0, 0, 21]
  ]

def cTauRaw : TIndex → QRaw :=
  ![
    ![9, 0, 0, 17, 0, 0, 0, 0, 0, 0, 20],
    ![13, 0, 0, 0, 15, 0, 0, 0, 0, 18, 0],
    ![19, 0, 0, 0, 0, 0, 12, 0, 15, 0, 0],
    ![0, 8, 16, 0, 0, 0, 0, 0, 0, 0, 22],
    ![0, 18, 0, 0, 0, 11, 0, 0, 17, 0, 0],
    ![0, 20, 0, 0, 0, 0, 10, 16, 0, 0, 0],
    ![0, 0, 11, 13, 0, 0, 0, 0, 0, 22, 0],
    ![0, 0, 19, 0, 0, 9, 0, 18, 0, 0, 0],
    ![0, 0, 0, 16, 9, 0, 0, 0, 21, 0, 0],
    ![0, 0, 0, 0, 22, 3, 21, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 21, 0, 6, 19]
  ]

def cTauData : Prop :=
  ∀ i : TIndex,
    qEmbed (cTau i) = cTauRaw i ∧ qMoment (cTauRaw i)

/-- The eleven base directions and their exact finite-difference labels. -/
def dTau : TIndex → Fibre :=
  ![
    ![1, 2, 3],
    ![1, 3, 4],
    ![1, 1, 2],
    ![1, 4, 16],
    ![1, 8, 1],
    ![1, 12, 9],
    ![1, 9, 8],
    ![1, 18, 12],
    ![1, 16, 13],
    ![1, 13, 18],
    ![1, 6, 6]
  ]

def lambdaTau : TIndex → Scalar :=
  ![20, 1, 5, 12, 21, 7, 14, 13, 8, 17, 19]

def rhoTau : TIndex → Scalar :=
  ![9, 19, 13, 15, 2, 6, 3, 5, 11, 16, 1]

/-- The linear forms and their exact differential coefficients. -/
def ellCoefficient (t : Scalar) : Fin 3 → Scalar :=
  ![t ^ 3, t, -1]

def ellPolynomial (t : Scalar) : Polynomial :=
  MvPolynomial.C (t ^ 3) * MvPolynomial.X 0 +
    MvPolynomial.C t * MvPolynomial.X 1 - MvPolynomial.X 2

def primitiveDerivative (c : QCoord) (i : Fin 3) : Polynomial :=
  ∑ j : TIndex,
    MvPolynomial.C (qEmbed c j) * (ellPolynomial (tValues j)) ^ 22 *
      MvPolynomial.C (ellCoefficient (tValues j) i)

/-- Exactness, homogeneity, and zero normalization of the linearly chosen
Cartier primitive. -/
def primitiveData
    (I : QCoord →ₗ[Scalar] Polynomial) : Prop :=
  (∀ c : QCoord, ∀ i : Fin 3,
    MvPolynomial.pderiv i (I c) = primitiveDerivative c i) ∧
    (∀ c : QCoord, MvPolynomial.IsHomogeneous (I c) 23) ∧
      (∀ c : QCoord,
        MvPolynomial.eval (fun _ : Fin 3 => (0 : Scalar)) (I c) = 0)

def primitiveShear
    (I : QCoord →ₗ[Scalar] Polynomial) (s : Fibre → A) : Prop :=
  ∀ x : Fibre, ∀ c : QCoord,
    s x c = MvPolynomial.eval x (I c)

/-- The eight doubled marker vectors and their signed support. -/
def markerSeeds : Fin 8 → Fibre :=
  ![
    ![1, 0, 0],
    ![0, 1, 0],
    ![0, 0, 1],
    ![1, 1, 0],
    ![1, 2, 0],
    ![1, 0, 1],
    ![1, 0, 3],
    ![1, 1, 1]
  ]

def markerSet : Set Fibre :=
  {m | ∃ i : Fin 8,
    m = (2 : Scalar) • markerSeeds i ∨
      m = -((2 : Scalar) • markerSeeds i)}

def baseSupport : Set Fibre :=
  markerSet ∪ Set.range dTau ∪ Set.range (fun i : TIndex => -dTau i)

def baseSupportData : Prop :=
  Set.ncard markerSet = 16 ∧
    Set.ncard baseSupport = 38 ∧
      ¬ ∃ x v : Fibre,
        v ≠ 0 ∧
          Set.range (fun t : Scalar => x + t • v) ⊆ baseSupport

def markerStabilizerData : Prop :=
  ∀ β : Fibre ≃ₗ[Scalar] Fibre,
    β '' markerSet = markerSet ↔
      (∀ x : Fibre, β x = x) ∨
        (∀ x : Fibre, β x = -x)

def rowSet (i : TIndex) (q : Scalar) : Set V :=
  {p | p.2 = dTau i ∧ p.1 (cTau i) = q}

def markerConnection : Set V :=
  {p | p.2 ∈ markerSet}

def rowConnectionZero : Set V :=
  {p | ∃ i : TIndex,
    p ∈ rowSet i 0 ∨ -p ∈ rowSet i 0}

def rowConnectionLambda : Set V :=
  {p | ∃ i : TIndex,
    p ∈ rowSet i (lambdaTau i) ∨ -p ∈ rowSet i (lambdaTau i)}

def S0 : Set V := rowConnectionZero ∪ markerConnection
def S1 : Set V := rowConnectionLambda ∪ markerConnection

def identityFreeInverseClosed (S : Set V) : Prop :=
  0 ∉ S ∧ ∀ x : V, x ∈ S → -x ∈ S

def spansV (S : Set V) : Prop :=
  AddSubgroup.closure S = ⊤

def ordinaryCayleyGraph {W : Type*} [AddGroup W]
    (S : Set W) : SimpleGraph W :=
  SimpleGraph.fromRel (fun x y => y - x ∈ S)

def thetaFunction (s : Fibre → A) (p : V) : V :=
  (p.1 + s p.2, p.2)

def thetaData (s : Fibre → A) (θ : V ≃ V) : Prop :=
  (∀ p : V, θ p = thetaFunction s p) ∧
    θ 0 = 0 ∧
      (∀ p : V, θ (-p) = -θ p) ∧
        ∀ x y : V,
          y - x ∈ S0 ↔ θ y - θ x ∈ S1

def tensorColumn (i : TIndex) : TensorProduct Scalar QCoord Fibre :=
  TensorProduct.tmul Scalar (cTau i) (dTau i)

def tensorSpan : Submodule Scalar (TensorProduct Scalar QCoord Fibre) :=
  Submodule.span Scalar (Set.range tensorColumn)

def augmentedColumn (i : TIndex) :
    TensorProduct Scalar QCoord Fibre × Scalar :=
  (tensorColumn i, lambdaTau i)

def augmentedSpan : Submodule Scalar
    (TensorProduct Scalar QCoord Fibre × Scalar) :=
  Submodule.span Scalar (Set.range augmentedColumn)

def tensorCertificate : Prop :=
  (∑ i : TIndex, rhoTau i • tensorColumn i) = 0 ∧
    (∑ i : TIndex, rhoTau i * lambdaTau i) = 2 ∧
      (2 : Scalar) ≠ 0 ∧
        Module.finrank Scalar tensorSpan = 10 ∧
          Module.finrank Scalar augmentedSpan = 11

def noLinearTransport : Prop :=
  ¬ ∃ α : V ≃ₗ[Scalar] V, α '' S0 = S1

def ordinaryCayleyCI (W : Type*) [AddCommGroup W]
    [Module Scalar W] : Prop :=
  ∀ S T : Set W,
    0 ∉ S → (∀ x : W, x ∈ S → -x ∈ S) →
      0 ∉ T → (∀ x : W, x ∈ T → -x ∈ T) →
        Nonempty (SimpleGraph.Iso
          (ordinaryCayleyGraph S) (ordinaryCayleyGraph T)) →
          ∃ α : W ≃ₗ[Scalar] W, α '' S = T

def rank11AndPadding : Prop :=
  Module.finrank Scalar V = 11 ∧
    ¬ ordinaryCayleyCI V ∧
      ∀ r : ℕ, 11 ≤ r →
        ¬ ordinaryCayleyCI (Fin r → Scalar)

/-- Claim 61166: the retained explicit rank-eleven cubic-ridge construction,
its graph isomorphism and exact obstruction certificate, together with the
span-preserving padding to every larger `C₂₃`-rank. -/
def claim61166 : Prop :=
  momentCoordinateModel ∧
    momentRowsIndependent ∧
      cTauData ∧
        baseSupportData ∧
          markerStabilizerData ∧
            ∃ I : QCoord →ₗ[Scalar] Polynomial,
              ∃ s : Fibre → A,
                primitiveData I ∧
                  primitiveShear I s ∧
                    (∀ x : Fibre, s (-x) = -s x) ∧
                      (∀ i : TIndex, ∀ x : Fibre,
                        (s (x + dTau i) - s x) (cTau i) = lambdaTau i) ∧
                        ∃ θ : V ≃ V,
                          thetaData s θ ∧
                            identityFreeInverseClosed S0 ∧
                              identityFreeInverseClosed S1 ∧
                                spansV S0 ∧
                                  spansV S1 ∧
                                    tensorCertificate ∧
                                      noLinearTransport ∧
                                        rank11AndPadding

end

end MathlibPlus.Open.ResearchFormalization.Claim61166
