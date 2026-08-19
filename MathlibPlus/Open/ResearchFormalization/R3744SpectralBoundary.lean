import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R3744

noncomputable section

abbrev Nonagon := ZMod 9

/-- The polygon adjacency relation on the nine cyclic points. -/
def cycleEdge (x y : Nonagon) : Prop :=
  x ≠ y ∧ (y = x + 1 ∨ y = x - 1)

def cycleAdjacency (x y : Nonagon) : ℝ := by
  classical
  exact if cycleEdge x y then 1 else 0

/-- The adjacency matrix H of the nonagon cycle. -/
def H : Matrix Nonagon Nonagon ℝ := fun x y => cycleAdjacency x y

def allOnes : Matrix Nonagon Nonagon ℝ := fun _ _ => 1

def kappa (x y : Nonagon) : ℝ := by
  classical
  exact if x = y then 0 else if cycleEdge x y then 1 else 2

/-- Incidence of the nine unique four-point classes, with centres as rows. -/
def incidenceMatrix (classes : Nonagon → Finset Nonagon) :
    Matrix Nonagon Nonagon ℝ :=
  fun c x => if x ∈ classes c then 1 else 0

def pointMultiplicity (classes : Nonagon → Finset Nonagon)
    (x y : Nonagon) : ℝ :=
  ∑ c : Nonagon,
    incidenceMatrix classes c x * incidenceMatrix classes c y

def centreMultiplicity (classes : Nonagon → Finset Nonagon)
    (c d : Nonagon) : ℝ :=
  ∑ x : Nonagon,
    incidenceMatrix classes c x * incidenceMatrix classes d x

def pointDeficit (classes : Nonagon → Finset Nonagon)
    (x y : Nonagon) : ℝ :=
  if x = y then 0 else kappa x y - pointMultiplicity classes x y

def centreDeficit (classes : Nonagon → Finset Nonagon)
    (c d : Nonagon) : ℝ :=
  if c = d then 0 else kappa c d - centreMultiplicity classes c d

def pointDeficitMatrix (classes : Nonagon → Finset Nonagon) :
    Matrix Nonagon Nonagon ℝ := fun x y => pointDeficit classes x y

def centreDeficitMatrix (classes : Nonagon → Finset Nonagon) :
    Matrix Nonagon Nonagon ℝ := fun c d => centreDeficit classes c d

/-- The all-unique-four incidence and capacity hypotheses from R-3744.3--4. -/
def allUniqueFourIncidenceData
    (classes : Nonagon → Finset Nonagon) : Prop :=
  let A := incidenceMatrix classes
  (∀ c, c ∉ classes c) ∧
    (∀ c, (classes c).card = 4) ∧
    (∀ c, ∑ x : Nonagon, A c x = 4) ∧
    (∀ x, ∑ c : Nonagon, A c x = 4) ∧
    (∀ x y, x ≠ y → pointMultiplicity classes x y ≤ kappa x y) ∧
    (∀ c d, c ≠ d → centreMultiplicity classes c d ≤ kappa c d)

def weightedDeficitDegree (D : Matrix Nonagon Nonagon ℝ) (x : Nonagon) : ℝ :=
  ∑ y : Nonagon, if x = y then 0 else D x y

def positiveDeficitEdge (D : Matrix Nonagon Nonagon ℝ)
    (x y : Nonagon) : Prop := x ≠ y ∧ 0 < D x y

/-- A symmetric nonnegative weighted 2-factor, with its integral edge weights. -/
def weightedDeficitTwoFactor (D : Matrix Nonagon Nonagon ℝ) : Prop :=
  (∀ x, D x x = 0) ∧
    (∀ x y, D x y = D y x) ∧
    (∀ x y, x ≠ y → 0 ≤ D x y) ∧
    (∀ x y, D x y = 0 ∨ D x y = 1 ∨ D x y = 2) ∧
    (∀ x, weightedDeficitDegree D x = 2)

def noDeficitEdgeAcross (D : Matrix Nonagon Nonagon ℝ)
    (S : Finset Nonagon) : Prop :=
  ∀ x ∈ S, ∀ y ∉ S, D x y = 0

/-- Being a union of connected components of the positive-deficit support. -/
def unionOfDeficitComponents (D : Matrix Nonagon Nonagon ℝ)
    (S : Finset Nonagon) : Prop :=
  noDeficitEdgeAcross D S

def supportReachableWithin (D : Matrix Nonagon Nonagon ℝ)
    (S : Finset Nonagon) (x y : Nonagon) : Prop :=
  Relation.ReflTransGen (fun u v : Nonagon => positiveDeficitEdge D u v) x y ∧
    x ∈ S ∧ y ∈ S

def simpleCycleComponent (D : Matrix Nonagon Nonagon ℝ)
    (S : Finset Nonagon) : Prop := by
  classical
  exact
    S.Nonempty ∧ noDeficitEdgeAcross D S ∧
      (∀ x ∈ S,
        (Finset.univ.filter
          (fun y => y ∈ S ∧ positiveDeficitEdge D x y)).card = 2) ∧
      (∀ x ∈ S, ∀ y ∈ S, supportReachableWithin D S x y)

def hasOddSimpleCycleComponent (D : Matrix Nonagon Nonagon ℝ) : Prop :=
  ∃ S : Finset Nonagon,
    simpleCycleComponent D S ∧ Odd S.card

def weightedGraphCospectral
    (G K : Matrix Nonagon Nonagon ℝ) : Prop := G.charpoly = K.charpoly

def posSemidefiniteOnOneOrthogonal
    (M : Matrix Nonagon Nonagon ℝ) : Prop :=
  (∀ x y, M x y = M y x) ∧
    ∀ v : Nonagon → ℝ,
      (∑ x : Nonagon, v x = 0) →
        0 ≤ dotProduct v (M.mulVec v)

def cycleBoundary (S : Finset Nonagon) : ℕ := by
  classical
  exact
    ∑ x ∈ S,
      (Finset.univ.filter (fun y => y ∉ S ∧ cycleEdge x y)).card

def cutBoundFor (S : Finset Nonagon) : Prop :=
  (2 * (S.card : ℝ) * (9 - (S.card : ℝ))) / 9 ≤
    (cycleBoundary S : ℝ)

/-- Claim 47906: the exact Gram identities, spectral boundary, and cut bound
for the all-unique-four nonagon incidence carrier. -/
def claim47906_exactGramSpectralBoundary : Prop :=
  ∀ classes : Nonagon → Finset Nonagon,
    allUniqueFourIncidenceData classes →
    let A := incidenceMatrix classes
    let DP := pointDeficitMatrix classes
    let DC := centreDeficitMatrix classes
    (weightedDeficitTwoFactor DP ∧
      weightedDeficitTwoFactor DC ∧
      hasOddSimpleCycleComponent DP ∧
      hasOddSimpleCycleComponent DC) ∧
    (DP = Matrix.transpose DP ∧ DC = Matrix.transpose DC) ∧
    (Matrix.transpose A * A =
      (2 : ℝ) • (1 : Matrix Nonagon Nonagon ℝ) +
        (2 : ℝ) • allOnes - H - DP) ∧
    (A * Matrix.transpose A =
      (2 : ℝ) • (1 : Matrix Nonagon Nonagon ℝ) +
        (2 : ℝ) • allOnes - H - DC) ∧
    weightedGraphCospectral (H + DP) (H + DC) ∧
    posSemidefiniteOnOneOrthogonal
      ((2 : ℝ) • (1 : Matrix Nonagon Nonagon ℝ) - H - DP) ∧
    posSemidefiniteOnOneOrthogonal
      ((2 : ℝ) • (1 : Matrix Nonagon Nonagon ℝ) - H - DC) ∧
    (∀ S : Finset Nonagon,
      (unionOfDeficitComponents DP S ∨ unionOfDeficitComponents DC S) →
        cutBoundFor S) ∧
    (∀ S : Finset Nonagon,
      (simpleCycleComponent DP S ∨ simpleCycleComponent DC S) →
        (S.card = 4 ∨ S.card = 5) → 6 ≤ cycleBoundary S)

end

end MathlibPlus.Open.ResearchFormalization.R3744
