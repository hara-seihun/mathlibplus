import Mathlib

open scoped BigOperators
open Classical
noncomputable section

namespace MathlibPlus.Open.Research.R2170

abbrev CubeVertex (m : ℕ) := Fin m → Bool

/-- The literal edge relation of the Boolean `m`-cube. -/
def cubeGraph (m : ℕ) : SimpleGraph (CubeVertex m) :=
  SimpleGraph.fromRel (fun x y =>
    ∃ i : Fin m, x i ≠ y i ∧ ∀ j : Fin m, j ≠ i → x j = y j)

/-- A literal graph on the cube is C4-free when it is a subgraph of the cube
and has no four pairwise-distinct cyclic vertices. -/
def literalC4Free (m : ℕ) (G : SimpleGraph (CubeVertex m)) : Prop :=
  (∀ ⦃x y : CubeVertex m⦄, G.Adj x y → (cubeGraph m).Adj x y) ∧
    ¬ ∃ a b c d : CubeVertex m,
      a ≠ b ∧ b ≠ c ∧ c ≠ d ∧ d ≠ a ∧ a ≠ c ∧ b ≠ d ∧
        G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a

/-- The finite edge count of a graph on a finite vertex type. -/
noncomputable def edgeCount {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ :=
  G.edgeSet.ncard

/-- The cube edge count in the normalization used by the source. -/
def cubeEdgeCount (m : ℕ) : ℝ :=
  (m : ℝ) * (2 : ℝ) ^ (m - 1)

/-- The extremal number of literal C4-free subgraphs of the cube. -/
noncomputable def cubeExtremal (m : ℕ) : ℝ :=
  sSup {a : ℝ | ∃ G : SimpleGraph (CubeVertex m), literalC4Free m G ∧
    a = edgeCount G}

abbrev PositiveCubeDimension := {m : ℕ // 1 ≤ m}

/-- The normalized finite extremal density. -/
def alpha (m : PositiveCubeDimension) : ℝ :=
  cubeExtremal m.1 / cubeEdgeCount m.1

/-- The asymptotic extremal value, as the infimum of the normalized sequence. -/
noncomputable def alphaInfinity : ℝ :=
  sInf (Set.range alpha)

/-- A coordinate face selects distinct target coordinates, uses each source
coordinate at its selected target coordinate exactly once, and fixes every
other target coordinate. -/
def coordinateFace {r m : ℕ} (e : CubeVertex r → CubeVertex m) : Prop :=
  ∃ ι : Fin r → Fin m, Function.Injective ι ∧
    ∃ b : Fin m → Bool,
      (∀ i : Fin r, ∀ x : CubeVertex r, e x (ι i) = x i) ∧
      (∀ j : Fin m, (∀ i : Fin r, ι i ≠ j) →
        ∀ x : CubeVertex r, e x j = b j)

/-- Restriction of a literal cube graph to a coordinate face. -/
def restrictToFace {r m : ℕ} (e : CubeVertex r → CubeVertex m)
    (G : SimpleGraph (CubeVertex m)) : SimpleGraph (CubeVertex r) :=
  G.comap e

/-- A finite point-mass probability law. -/
def finiteProbabilityLaw {α : Type*} [Fintype α] (ν : α → ℝ) : Prop :=
  (∀ a, 0 ≤ ν a) ∧ ∑ a, ν a = 1

/-- Pullback of a cube graph along a vertex map. -/
def pullbackGraph {V W : Type*} (e : V → W) (G : SimpleGraph W) : SimpleGraph V :=
  G.comap e

/-- Cube translations act on Boolean words by coordinatewise xor. -/
def cubeTranslation {m : ℕ} (t : CubeVertex m) : CubeVertex m → CubeVertex m :=
  fun x i => Bool.xor (x i) (t i)

/-- Coordinate permutations act by pullback on Boolean words. -/
def cubeCoordinatePermutation {m : ℕ} (σ : Equiv.Perm (Fin m)) :
    CubeVertex m → CubeVertex m :=
  fun x i => x (σ i)

/-- The expected relative edge density of a finite law in a positive cube
 dimension. -/
def expectedRelativeDensity
    (ν : ∀ m : ℕ, SimpleGraph (CubeVertex m) → ℝ)
    (m : PositiveCubeDimension) : ℝ :=
  ∑ G : SimpleGraph (CubeVertex m.1),
    ν m.1 G * (edgeCount G : ℝ) / cubeEdgeCount m.1

/-- Selection probability of an individual cube edge under a finite law. -/
def edgeSelectionProbability
    (ν : ∀ m : ℕ, SimpleGraph (CubeVertex m) → ℝ)
    (m : PositiveCubeDimension) (e : Sym2 (CubeVertex m.1)) : ℝ :=
  ∑ G : SimpleGraph (CubeVertex m.1),
    ν m.1 G * if e ∈ (cubeGraph m.1).edgeSet ∧ e ∈ G.edgeSet then 1 else 0

/-- The common density attached to a coherent law, including the expected
relative density and the fixed-edge selection probability. -/
def hasCommonDensity
    (ν : ∀ m : ℕ, SimpleGraph (CubeVertex m) → ℝ) (p : ℝ) : Prop :=
  (∀ m : PositiveCubeDimension, expectedRelativeDensity ν m = p) ∧
    (∀ m : PositiveCubeDimension, ∀ e : Sym2 (CubeVertex m.1),
      e ∈ (cubeGraph m.1).edgeSet → edgeSelectionProbability ν m e = p)

/-- The exact finite-law support and cube-exchangeability conditions. -/
def cubeExchangeableProjectiveLaw
    (ν : ∀ m : ℕ, SimpleGraph (CubeVertex m) → ℝ) : Prop :=
  (∀ m : ℕ, finiteProbabilityLaw (ν m)) ∧
    (∀ m : ℕ, ∀ G : SimpleGraph (CubeVertex m),
      ν m G ≠ 0 → literalC4Free m G) ∧
    (∀ m : ℕ, ∀ G : SimpleGraph (CubeVertex m), ∀ t : CubeVertex m,
      ν m (pullbackGraph (cubeTranslation t) G) = ν m G) ∧
    (∀ m : ℕ, ∀ G : SimpleGraph (CubeVertex m), ∀ σ : Equiv.Perm (Fin m),
      ν m (pullbackGraph (cubeCoordinatePermutation σ) G) = ν m G) ∧
    (∀ r m : ℕ, ∀ _h : r ≤ m,
      ∀ e : CubeVertex r → CubeVertex m, coordinateFace e →
        ∀ H : SimpleGraph (CubeVertex r),
          ν r H = ∑ G : SimpleGraph (CubeVertex m),
            if restrictToFace e G = H then ν m G else 0)

/-- The finite automorphism group used in symmetrization. -/
abbrev CubeAutomorphism (m : ℕ) :=
  {σ : Equiv.Perm (CubeVertex m) //
    ∀ x y : CubeVertex m,
      (cubeGraph m).Adj (σ x) (σ y) ↔ (cubeGraph m).Adj x y}

/-- Uniform orbit mass obtained by symmetrizing one literal cube graph under
all cube automorphisms. -/
def symmetrizedMass (m : ℕ) (G₀ H : SimpleGraph (CubeVertex m)) : ℝ :=
  (∑ σ : CubeAutomorphism m,
    if pullbackGraph σ.1 G₀ = H then (1 : ℝ) else 0) /
    Fintype.card (CubeAutomorphism m)

/-- The canonical fixed coordinate face consisting of the first `m`
coordinates, with all remaining coordinates fixed to false. -/
def canonicalFace (m n : ℕ) : CubeVertex m → CubeVertex n :=
  fun x j => if h : j.1 < m then x ⟨j.1, h⟩ else false

/-- The relative edge density of a symmetrized finite law. -/
def symmetrizedRelativeDensity (m : ℕ)
    (G₀ : SimpleGraph (CubeVertex m)) : ℝ :=
  ∑ H : SimpleGraph (CubeVertex m),
    symmetrizedMass m G₀ H * (edgeCount H : ℝ) / cubeEdgeCount m

/-- The law on an `m`-face obtained by restricting the symmetrized `n`-cube
law to the canonical fixed face. -/
def restrictedSymmetrizedMass (m n : ℕ)
    (G₀ : SimpleGraph (CubeVertex n)) (H : SimpleGraph (CubeVertex m)) : ℝ :=
  ∑ G : SimpleGraph (CubeVertex n),
    symmetrizedMass n G₀ G *
      if restrictToFace (canonicalFace m n) G = H then (1 : ℝ) else 0

/-- The diagonal compactness statement produced by extremal graphs,
symmetrization, fixed-face restriction, and finite-simplex convergence. -/
def extremizerProjectiveCompactness : Prop :=
  ∃ (G : ∀ n : PositiveCubeDimension, SimpleGraph (CubeVertex n.1)),
    (∀ n : PositiveCubeDimension,
      literalC4Free n.1 (G n) ∧
        (edgeCount (G n) : ℝ) = cubeExtremal n.1) ∧
    (∀ n : PositiveCubeDimension,
      finiteProbabilityLaw (symmetrizedMass n.1 (G n)) ∧
        (∀ H : SimpleGraph (CubeVertex n.1),
          symmetrizedMass n.1 (G n) H ≠ 0 → literalC4Free n.1 H) ∧
        symmetrizedRelativeDensity n.1 (G n) = alpha n) ∧
    ∃ (s : ℕ → PositiveCubeDimension)
      (ν : ∀ m : ℕ, SimpleGraph (CubeVertex m) → ℝ),
      StrictMono s ∧
      Filter.Tendsto (fun k : ℕ => (s k).1) Filter.atTop Filter.atTop ∧
      (∀ m : ℕ, ∀ k : ℕ, m ≤ (s k).1 →
        coordinateFace (canonicalFace m (s k).1)) ∧
      (∀ m : ℕ, ∀ n : PositiveCubeDimension, m ≤ n.1 →
        finiteProbabilityLaw (restrictedSymmetrizedMass m n.1 (G n)) ∧
        (∀ H : SimpleGraph (CubeVertex m),
          restrictedSymmetrizedMass m n.1 (G n) H ≠ 0 →
            literalC4Free m H)) ∧
      cubeExchangeableProjectiveLaw ν ∧
      hasCommonDensity ν alphaInfinity ∧
      ∀ m : ℕ, ∀ H : SimpleGraph (CubeVertex m),
        Filter.Tendsto
          (fun k : ℕ => restrictedSymmetrizedMass m (s k).1
            (G (s k)) H)
          Filter.atTop (nhds (ν m H))

/-- The density set of all coherent cube-exchangeable projective laws. -/
def projectiveDensitySet : Set ℝ :=
  {p : ℝ | ∃ ν : ∀ m : ℕ, SimpleGraph (CubeVertex m) → ℝ,
    cubeExchangeableProjectiveLaw ν ∧ hasCommonDensity ν p}

/-- In the present normalization, the original Erdős problem 86 is the
one-half upper-bound assertion for the asymptotic extremal value. -/
def erdosProblem86 : Prop :=
  alphaInfinity ≤ (1 / 2 : ℝ)

/-- Claim 31415: C4-freeness survives coordinate-face restriction, the
normalized extremal sequence is nonincreasing, and its limit is its infimum. -/
def claim31415_monotonicityOfAlpha : Prop :=
  (∀ r m : ℕ, 1 ≤ r → r ≤ m →
    ∀ (e : CubeVertex r → CubeVertex m), coordinateFace e →
      ∀ G : SimpleGraph (CubeVertex m), literalC4Free m G →
        literalC4Free r (restrictToFace e G)) ∧
  (∀ r m : PositiveCubeDimension, r ≤ m → alpha m ≤ alpha r) ∧
  Filter.Tendsto alpha Filter.atTop (nhds alphaInfinity) ∧
  IsGLB (Set.range alpha) alphaInfinity

/-- Claim 31417: every coherent projective law has common density at most
 every finite normalized extremal density and at most the asymptotic value. -/
def claim31417_projectiveDensityBound : Prop :=
  ∀ (ν : ∀ m : ℕ, SimpleGraph (CubeVertex m) → ℝ) (p : ℝ),
    cubeExchangeableProjectiveLaw ν →
      hasCommonDensity ν p →
        (∀ m : PositiveCubeDimension, p ≤ alpha m) ∧ p ≤ alphaInfinity

/-- Claim 31419: the supremum of coherent projective densities is exactly the
asymptotic extremal value, and the one-half projective assertion is precisely
Erdős problem 86. -/
def claim31419_projectiveSupremumEquivalence : Prop :=
  IsLUB projectiveDensitySet alphaInfinity ∧
    ((∀ (ν : ∀ m : ℕ, SimpleGraph (CubeVertex m) → ℝ) (p : ℝ),
      cubeExchangeableProjectiveLaw ν → hasCommonDensity ν p → p ≤ (1 / 2 : ℝ)) ↔
      erdosProblem86)

/-- Claim 31422: the all-order compactness statement for finite literal
C4-free cube graphs and all coherent projective invariant laws preserves the
full extremal value.  The declaration deliberately contains no one-half
upper-bound conclusion; the result is the compactness route-kill described in
the source scope boundary. -/
def claim31422_compactnessScope : Prop :=
  extremizerProjectiveCompactness ∧
    IsLUB projectiveDensitySet alphaInfinity

end MathlibPlus.Open.Research.R2170
