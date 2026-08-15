import Mathlib

open scoped BigOperators


namespace MathlibPlus.Open.FormalizationBatch

noncomputable section
open Classical

namespace Common

/-- The Boolean adjacency bit of a relation. -/
def adjBit {W : Type*} (A : W → W → Prop) (u w : W) : Bool :=
  decide (A u w)

/-- The degree of a vertex for a finite adjacency relation. -/
def finiteDegree {W : Type*} [Fintype W] [DecidableEq W]
    (A : W → W → Prop) (u : W) : ℕ :=
  (Finset.univ.filter (fun w => A u w)).card

/-- The common-neighbor count for a finite adjacency relation. -/
def commonNeighborCount {W : Type*} [Fintype W] [DecidableEq W]
    (A : W → W → Prop) (u w : W) : ℕ :=
  (Finset.univ.filter (fun z => A u z ∧ A w z)).card

/-- The number of edges internal to a finite set, counted once. -/
def internalEdgeCount {W : Type*} [Fintype W] [DecidableEq W]
    (A : W → W → Prop) (S : Finset W) : ℕ :=
  ((S.product S).filter (fun p => p.1 ≠ p.2 ∧ A p.1 p.2)).card / 2

/-- The number of edges crossing two disjoint finite sets. -/
def crossingEdgeCount {W : Type*} [DecidableEq W]
    (A : W → W → Prop) (S T : Finset W) : ℕ :=
  ((S.product T).filter (fun p => A p.1 p.2)).card

/-- The neighbor set as a finite set. -/
def neighborFinset {W : Type*} [Fintype W] [DecidableEq W]
    (A : W → W → Prop) (u : W) : Finset W :=
  Finset.univ.filter (fun w => A u w)

/-- Degree in the card obtained by deleting `v`, represented on the old carrier. -/
def deletedDegree {W : Type*} [Fintype W] [DecidableEq W]
    (A : W → W → Prop) (v u : W) : ℕ :=
  (Finset.univ.filter (fun w => w ≠ v ∧ A u w)).card

/-- Common-neighbor count in the card obtained by deleting `v`. -/
def deletedCommonNeighborCount {W : Type*} [Fintype W] [DecidableEq W]
    (A : W → W → Prop) (v u w : W) : ℕ :=
  (Finset.univ.filter (fun z => z ≠ v ∧ A u z ∧ A w z)).card

/-- Degree/common-neighbor profile of ordered distinct pairs. -/
def pairProfile {W : Type*} [Fintype W] [DecidableEq W]
    (A : W → W → Prop) (ε : Bool) (d e c : ℕ) : ℕ :=
  ((Finset.univ.product Finset.univ).filter (fun p =>
    p.1 ≠ p.2 ∧
    adjBit A p.1 p.2 = ε ∧
    finiteDegree A p.1 = d ∧
    finiteDegree A p.2 = e ∧
    commonNeighborCount A p.1 p.2 = c)).card

/-- Degree/common-neighbor profile of ordered pairs in a deleted card. -/
def deletedPairProfile {W : Type*} [Fintype W] [DecidableEq W]
    (A : W → W → Prop) (v : W) (ε : Bool) (d e c : ℕ) : ℕ :=
  ((Finset.univ.product Finset.univ).filter (fun p =>
    p.1 ≠ p.2 ∧ p.1 ≠ v ∧ p.2 ≠ v ∧
    adjBit A p.1 p.2 = ε ∧
    deletedDegree A v p.1 = d ∧
    deletedDegree A v p.2 = e ∧
    deletedCommonNeighborCount A v p.1 p.2 = c)).card

/-- The four outside-cell counts of an ordered distinct pair. -/
def pairCell12 {W : Type*} [Fintype W] [DecidableEq W]
    (A : W → W → Prop) (u w : W) : ℕ :=
  commonNeighborCount A u w

def pairCell1 {W : Type*} [Fintype W] [DecidableEq W]
    (A : W → W → Prop) (u w : W) : ℕ :=
  (Finset.univ.filter (fun z => z ≠ u ∧ z ≠ w ∧ A u z ∧ ¬ A w z)).card

def pairCell2 {W : Type*} [Fintype W] [DecidableEq W]
    (A : W → W → Prop) (u w : W) : ℕ :=
  (Finset.univ.filter (fun z => z ≠ u ∧ z ≠ w ∧ ¬ A u z ∧ A w z)).card

def pairCellEmpty {W : Type*} [Fintype W] [DecidableEq W]
    (A : W → W → Prop) (u w : W) : ℕ :=
  (Finset.univ.filter (fun z => z ≠ u ∧ z ≠ w ∧ ¬ A u z ∧ ¬ A w z)).card

/-- Pair profile indexed by the four cell counts, which are integers in the inverse formulas. -/
def fourCellProfile {W : Type*} [Fintype W] [DecidableEq W]
    (A : W → W → Prop) (ε : Bool)
    (c12 c1 c2 cEmpty : ℤ) : ℕ :=
  ((Finset.univ.product Finset.univ).filter (fun p =>
    p.1 ≠ p.2 ∧
    adjBit A p.1 p.2 = ε ∧
    (pairCell12 A p.1 p.2 : ℤ) = c12 ∧
    (pairCell1 A p.1 p.2 : ℤ) = c1 ∧
    (pairCell2 A p.1 p.2 : ℤ) = c2 ∧
    (pairCellEmpty A p.1 p.2 : ℤ) = cEmpty)).card

def epsilonInteger (ε : Bool) : ℤ := if ε then 1 else 0

/-- Host degree counts and deleted-card counts used by the card recurrences. -/
def hostDegreeCount {W : Type*} [Fintype W] [DecidableEq W]
    (A : W → W → Prop) (j : ℕ) : ℕ :=
  (Finset.univ.filter (fun u => finiteDegree A u = j)).card

def deletedDegreeCount {W : Type*} [Fintype W] [DecidableEq W]
    (A : W → W → Prop) (v : W) (j : ℕ) : ℕ :=
  (Finset.univ.filter (fun u => u ≠ v ∧ deletedDegree A v u = j)).card

def neighborHostDegreeCount {W : Type*} [Fintype W] [DecidableEq W]
    (A : W → W → Prop) (v : W) (j : ℕ) : ℕ :=
  (Finset.univ.filter (fun u => A v u ∧ finiteDegree A u = j)).card

/-- The adjacency relation of a graph with one new leaf `none` attached to `x`. -/
def leafAdjacency {V : Type*} (C : SimpleGraph V) (x : V) :
    Option V → Option V → Prop
  | none, none => False
  | none, some u => u = x
  | some u, none => u = x
  | some u, some w => C.Adj u w

/-- Ordered triples with their six root/pair relations exposed as a profile. -/
def rootedTripleProfile {V : Type*} [Fintype V] [DecidableEq V]
    (A : V → V → Prop) (x : V)
    (α β : Fin 3 → Bool) : ℕ :=
  (Finset.univ.filter (fun t : V × V × V =>
    let u := t.1
    let w := t.2.1
    let z := t.2.2
    u ≠ w ∧ u ≠ z ∧ w ≠ z ∧ u ≠ x ∧ w ≠ x ∧ z ≠ x ∧
    adjBit A x u = α 0 ∧ adjBit A x w = α 1 ∧ adjBit A x z = α 2 ∧
    adjBit A u w = β 0 ∧ adjBit A u z = β 1 ∧ adjBit A w z = β 2)).card

/-- The six internal pairs of an ordered quadruple. -/
def quadGramProfile {W : Type*} [Fintype W] [DecidableEq W]
    (A : W → W → Prop)
    (bits : Fin 6 → Bool) (degrees : Fin 4 → ℕ)
    (commons : Fin 6 → ℕ) : ℕ :=
  (Finset.univ.filter (fun t : W × W × W × W =>
    let a := t.1
    let b := t.2.1
    let c := t.2.2.1
    let d := t.2.2.2
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
    adjBit A a b = bits 0 ∧ adjBit A a c = bits 1 ∧
    adjBit A a d = bits 2 ∧ adjBit A b c = bits 3 ∧
    adjBit A b d = bits 4 ∧ adjBit A c d = bits 5 ∧
    finiteDegree A a = degrees 0 ∧ finiteDegree A b = degrees 1 ∧
    finiteDegree A c = degrees 2 ∧ finiteDegree A d = degrees 3 ∧
    commonNeighborCount A a b = commons 0 ∧
    commonNeighborCount A a c = commons 1 ∧
    commonNeighborCount A a d = commons 2 ∧
    commonNeighborCount A b c = commons 3 ∧
    commonNeighborCount A b d = commons 4 ∧
    commonNeighborCount A c d = commons 5)).card

/-- The degree/refined four-cell table of a finite graph. -/
def stronglyRegular {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (v k lam μ : ℕ) : Prop :=
  Fintype.card V = v ∧
  (∀ x, finiteDegree C.Adj x = k) ∧
  (∀ x y, x ≠ y → C.Adj x y → commonNeighborCount C.Adj x y = lam) ∧
  (∀ x y, x ≠ y → ¬ C.Adj x y → commonNeighborCount C.Adj x y = μ)

end Common

namespace K0087

/-- The divisor-lattice difference supplied by the admitted boundary-layer claims. -/
def divisorDifference (f : NNReal → ℂ) (y : NNReal) (k : ℕ) : ℂ :=
  ∑ d ∈ k.divisors, (ArithmeticFunction.moebius d : ℂ) * (f (y * (d : NNReal)) - f 0)

def divisorDifferenceTerm (f : NNReal → ℂ) (y : NNReal) (k : ℕ) : ℝ :=
  if 1 ≤ k then ‖divisorDifference f y k‖ ^ 2 / (k : ℝ) ^ 2 else 0

def linearWeightedL2BoundaryLayer8375 : Prop :=
  ∀ (f : NNReal → ℂ) (A : ℝ),
    (∀ x : NNReal, ‖f x - f 0‖ ≤ A * min (x : ℝ) 1) →
    ∀ y : NNReal, 0 < y → y ≤ 1 →
      Summable (divisorDifferenceTerm f y) ∧
      (∑' k : ℕ, divisorDifferenceTerm f y k) ≤ 32 * A ^ 2 * (y : ℝ)

/-- The common-multiple expansion of the divisor-difference square. -/
def exactCommonMultipleSquareExpansion8376 : Prop :=
  ∀ (f : NNReal → ℂ) (A : ℝ),
    (∀ x : NNReal, ‖f x - f 0‖ ≤ A * min (x : ℝ) 1) →
    ∀ y : NNReal, 0 < y → y ≤ 1 →
      ((∑' k : ℕ, divisorDifferenceTerm f y k : ℝ) : ℂ) =
        (∑' m : ℕ, if 1 ≤ m then (1 : ℝ) / (m : ℝ) ^ 2 else 0) *
        (∑' d : ℕ, ∑' e : ℕ,
          if 1 ≤ d ∧ 1 ≤ e then
            (ArithmeticFunction.moebius d : ℂ) * (ArithmeticFunction.moebius e : ℂ) *
              (f (y * (d : NNReal)) - f 0) *
              star (f (y * (e : NNReal)) - f 0) /
              (Nat.lcm d e : ℂ) ^ 2
          else 0)

end K0087

namespace K0088

/-- The physical inverse-Mellin divisor kernel. -/
def divisorKernelDelta (y : NNReal) (k : ℕ) : ℝ :=
  ∑ d ∈ k.divisors, (ArithmeticFunction.moebius d : ℝ) * Real.exp (- (y : ℝ) * (d : ℝ))

def divisorKernelTerm (y : NNReal) (k : ℕ) : ℝ :=
  if 1 ≤ k then
    (divisorKernelDelta y k - if k = 1 then 1 else 0) ^ 2 / (k : ℝ) ^ 2
  else 0

def linearL2BoundaryLayerForDivisorDefects8399 : Prop :=
  (∀ y : NNReal, 0 < y → y ≤ 1 →
    Summable (divisorKernelTerm y) ∧
    (∑' k : ℕ, divisorKernelTerm y k) ≤ 32 * (y : ℝ)) ∧
  (∀ (f : NNReal → ℂ) (A : ℝ),
    (∀ x : NNReal, ‖f x - f 0‖ ≤ A * min (x : ℝ) 1) →
    ∀ y : NNReal, 0 < y → y ≤ 1 →
      Summable (K0087.divisorDifferenceTerm f y) ∧
      (∑' k : ℕ, K0087.divisorDifferenceTerm f y k) ≤
        32 * A ^ 2 * (y : ℝ))

end K0088

namespace R0385

open Common

/-- Degree/common-neighbor refinement and the four-cell pair table are equivalent. -/
def degreeCommonNeighborRefinement20717 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : Prop :=
  (∀ u w, u ≠ w →
    let ε := adjBit G.Adj u w
    let d := finiteDegree G.Adj u
    let e := finiteDegree G.Adj w
    let c := commonNeighborCount G.Adj u w
    (pairCell1 G.Adj u w : ℤ) = (d : ℤ) - epsilonInteger ε - (c : ℤ) ∧
    (pairCell2 G.Adj u w : ℤ) = (e : ℤ) - epsilonInteger ε - (c : ℤ) ∧
    (pairCellEmpty G.Adj u w : ℤ) = (Fintype.card V : ℤ) - 2 - (d : ℤ) -
      (e : ℤ) + 2 * epsilonInteger ε + (c : ℤ)) ∧
  (∀ ε d e c,
    pairProfile G.Adj ε d e c =
      fourCellProfile G.Adj ε (c : ℤ)
        ((d : ℤ) - epsilonInteger ε - (c : ℤ))
        ((e : ℤ) - epsilonInteger ε - (c : ℤ))
        ((Fintype.card V : ℤ) - 2 - (d : ℤ) - (e : ℤ) +
          2 * epsilonInteger ε + (c : ℤ))) ∧
  (∀ ε c12 c1 c2 cEmpty,
    0 ≤ c12 → 0 ≤ c1 → 0 ≤ c2 → 0 ≤ cEmpty →
    cEmpty = (Fintype.card V : ℤ) - 2 -
        (c12 + c1 + epsilonInteger ε) -
        (c12 + c2 + epsilonInteger ε) +
        2 * epsilonInteger ε + c12 →
      fourCellProfile G.Adj ε c12 c1 c2 cEmpty =
        pairProfile G.Adj ε
          (Int.toNat (c12 + c1 + epsilonInteger ε))
          (Int.toNat (c12 + c2 + epsilonInteger ε))
          (Int.toNat c12))

/-- The degree-count change caused by deleting a vertex. -/
def cardDegreeCountChange20719 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : Prop :=
  ∀ v j,
    let k := finiteDegree G.Adj v
    (deletedDegreeCount G.Adj v j : ℤ) =
      (hostDegreeCount G.Adj j : ℤ) -
        (if k = j then (1 : ℤ) else 0) -
        (neighborHostDegreeCount G.Adj v j : ℤ) +
        (neighborHostDegreeCount G.Adj v (j + 1) : ℤ)

/-- The triangular inversion of the neighbor-degree vector from a card. -/
def triangularNeighborDegreeInversion20720 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : Prop :=
  ∀ v,
    neighborHostDegreeCount G.Adj v 0 = 0 ∧
    (∀ j,
      (neighborHostDegreeCount G.Adj v (j + 1) : ℤ) =
        (neighborHostDegreeCount G.Adj v j : ℤ) +
          (deletedDegreeCount G.Adj v j : ℤ) -
          (hostDegreeCount G.Adj j : ℤ) +
          (if finiteDegree G.Adj v = j then (1 : ℤ) else 0)) ∧
    (∀ b : ℕ → ℤ,
      b 0 = 0 →
      (∀ j,
        b (j + 1) = b j + (deletedDegreeCount G.Adj v j : ℤ) -
          (hostDegreeCount G.Adj j : ℤ) +
          (if finiteDegree G.Adj v = j then (1 : ℤ) else 0)) →
      ∀ j, b j = (neighborHostDegreeCount G.Adj v j : ℤ))

/-- The exact recurrence for the sum of all deleted-card pair profiles. -/
def exactSummedCardPairRecurrence20723 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : Prop :=
  ∀ ε d e c,
    (∑ v : V, (deletedPairProfile G.Adj v ε d e c : ℤ)) =
      ((Fintype.card V : ℤ) - 2 - (d : ℤ) - (e : ℤ) +
          2 * epsilonInteger ε + (c : ℤ)) *
        (pairProfile G.Adj ε d e c : ℤ) +
      ((d : ℤ) + 1 - epsilonInteger ε - (c : ℤ)) *
        (pairProfile G.Adj ε (d + 1) e c : ℤ) +
      ((e : ℤ) + 1 - epsilonInteger ε - (c : ℤ)) *
        (pairProfile G.Adj ε d (e + 1) c : ℤ) +
      ((c : ℤ) + 1) *
        (pairProfile G.Adj ε (d + 1) (e + 1) (c + 1) : ℤ)

end R0385

namespace R0388

open Common

/-- The ordered triple Gram census specification. -/
def orderedTripleGramCensus20774 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : Prop :=
  ∃! Γ : (Fin 3 → Bool) → (Fin 3 → ℕ) → (Fin 3 → ℕ) → ℕ,
    ∀ α d c, Γ α d c =
      (Finset.univ.filter (fun t : V × V × V =>
        let u := t.1
        let w := t.2.1
        let z := t.2.2
        u ≠ w ∧ u ≠ z ∧ w ≠ z ∧
        adjBit G.Adj u w = α 0 ∧ adjBit G.Adj u z = α 1 ∧
        adjBit G.Adj w z = α 2 ∧
        finiteDegree G.Adj u = d 0 ∧ finiteDegree G.Adj w = d 1 ∧
        finiteDegree G.Adj z = d 2 ∧
        commonNeighborCount G.Adj u w = c 0 ∧
        commonNeighborCount G.Adj u z = c 1 ∧
        commonNeighborCount G.Adj w z = c 2)).card

/-- Incidence counts for a strongly regular graph split at a vertex. -/
def neighborNonneighborIncidence20777 {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (v k lam μ : ℕ) : Prop :=
  stronglyRegular C v k lam μ →
    ∀ x,
      let N := neighborFinset C.Adj x
      let M := Finset.univ \ (N ∪ {x})
      ((internalEdgeCount C.Adj N : ℚ) = (k : ℚ) * (lam : ℚ) / 2) ∧
      ((crossingEdgeCount C.Adj N M : ℚ) =
        (k : ℚ) * ((k : ℚ) - 1 - (lam : ℚ))) ∧
      ((internalEdgeCount C.Adj M : ℚ) =
        ((v : ℚ) - (k : ℚ) - 1) * ((k : ℚ) - (μ : ℚ)) / 2)

/-- A leaf attached only to `x` detects exactly the neighbors of `x`. -/
def leafCommonNeighborIndicator20778 {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) : Prop :=
  ∀ x u,
    commonNeighborCount (leafAdjacency C x) (none : Option V) (some u) =
      if C.Adj x u then 1 else 0

/-- The rooted four-profile specification. -/
def orderedRootedFourProfile20783 {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) : Prop :=
  ∀ x, ∃! ρ : (Fin 3 → Bool) → (Fin 3 → Bool) → ℕ,
    ∀ α β, ρ α β = rootedTripleProfile C.Adj x α β

/-- The quadruple Gram census specification. -/
def quadrupleGramCensus20784 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : Prop :=
  ∃! Γ : (Fin 6 → Bool) → (Fin 4 → ℕ) → (Fin 6 → ℕ) → ℕ,
    ∀ bits degrees commons,
      Γ bits degrees commons = quadGramProfile G.Adj bits degrees commons

/-- Equality of leaf quadruple censuses is equivalent to equality of rooted profiles. -/
def quadrupleCensusEquivalenceWithRootedProfile20785
    {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (v k lam μ : ℕ) : Prop :=
  stronglyRegular C v k lam μ →
    2 ≤ k →
    ∀ x y,
      ((fun bits degrees commons =>
          quadGramProfile (leafAdjacency C x) bits degrees commons) =
        (fun bits degrees commons =>
          quadGramProfile (leafAdjacency C y) bits degrees commons)) ↔
      ((fun α β => rootedTripleProfile C.Adj x α β) =
        (fun α β => rootedTripleProfile C.Adj y α β))

end R0388

end
end MathlibPlus.Open.FormalizationBatch
