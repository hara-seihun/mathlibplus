import Mathlib

<<<<<<< ours
<<<<<<< ours
namespace MathlibPlus.Open.ResearchFormalizationBatch019ffedd

noncomputable section

/-- The generalized even-monomial kernel from Claim 18525. -/
def generalizedEvenMonomialKernel (y : ℝ) (j : ℕ) : ℝ :=
  y ^ (2 * j) / (Nat.factorial (2 * j) : ℝ)

/-- Claim 18525: the generalized even-monomial kernel is strictly totally positive. -/
def claim18525 : Prop :=
  ∀ (r : ℕ), 0 < r →
    ∀ (y : Fin r → ℝ), (∀ i, 0 < y i) → StrictMono y →
      ∀ (d : Fin r → ℕ), StrictMono d →
        0 < Matrix.det (fun i j => generalizedEvenMonomialKernel (y i) (d j))

/-- Strict total positivity on ordered natural-number rows and columns. -/
def batchStrictTP (K : ℕ → ℕ → ℝ) : Prop :=
  ∀ (r : ℕ), 0 < r →
    ∀ (x d : Fin r → ℕ), StrictMono x → StrictMono d →
      0 < Matrix.det (fun i j => K (x i) (d j))

/-- Strict total positivity on ordered cuts and nonnegative radii. -/
def batchStrictEvaluationTP (K : ℕ → ℝ → ℝ) : Prop :=
  ∀ (r : ℕ), 0 < r →
    ∀ (x : Fin r → ℕ), StrictMono x →
      ∀ (z : Fin r → ℝ), (∀ i, 0 ≤ z i) → StrictMono z →
        0 < Matrix.det (fun i j => K (x i) (z j))

/-- The evaluation kernel in Claim 18528. -/
def batchEvaluationKernel (A : ℕ → ℕ → ℝ) (M : ℕ) (z : ℝ) : ℝ :=
  ∑' j : ℕ, A M j * z ^ (2 * j)

/-- Claim 18528: coefficient strict TP implies evaluation-kernel strict TP. -/
def claim18528 : Prop :=
  ∀ (A : ℕ → ℕ → ℝ), batchStrictTP A →
    batchStrictEvaluationTP (batchEvaluationKernel A)

/-- Claim 18543: the Laplace representation of the Borel-band kernel. -/
def claim18543 : Prop :=
  ∀ (a q u : ℝ), 0 < a → 0 < q → 0 < 1 + q * u →
    let ρ : ℝ := q⁻¹
    (1 + q * u) ^ (-a) =
      (ρ ^ a / Real.Gamma a) *
        ∫ v in Set.Ioi (0 : ℝ),
          v ^ (a - 1) * Real.exp (-ρ * v) * Real.exp (-u * v)

/-- Claim 18544: strict total positivity of the Borel-band kernel. -/
def claim18544 : Prop :=
  ∀ (a : ℝ), 0 < a →
    ∀ (r : ℕ), 0 < r →
      ∀ (q u : Fin r → ℝ),
        (∀ i, 0 < q i) →
        (∀ i j, i < j → q j < q i) →
        (∀ i, 0 < u i) →
        (∀ i j, i < j → u i < u j) →
          0 < Matrix.det (fun i j => (1 + q i * u j) ^ (-a))

/-- The Vandermonde factor used in Claim 18556. -/
def batchVandermonde {r : ℕ} (y : Fin r → ℝ) : ℝ :=
  ∏ i : Fin r, ∏ j : Fin r, if i < j then y j - y i else 1

/-- The elementary symmetric polynomial used in Claim 18556. -/
def batchElementarySymmetric {r : ℕ} (y : Fin r → ℝ) (k : ℕ) : ℝ :=
  ∑ S ∈ (Finset.univ : Finset (Finset (Fin r))).filter (fun S => S.card = k),
    ∏ i ∈ S, y i

/-- The exponents left after omitting s+r-k from the consecutive window. -/
def batchOmittedExponent (r s k : ℕ) (j : Fin r) : ℕ :=
  if j.val < r - k then s + j.val else s + j.val + 1

/-- Claim 18556: the omitted-column alternant identity. -/
def claim18556 : Prop :=
  ∀ (r s k : ℕ), k ≤ r →
    ∀ (y : Fin r → ℝ),
      Matrix.det (fun i j => y i ^ batchOmittedExponent r s k j) =
        batchVandermonde y * (∏ i : Fin r, y i) ^ s *
          batchElementarySymmetric y k

/-- The r-row minor of A used for c_{s,k}(J) in Claim 18557. -/
def batchWindowMinor {r : ℕ} (A : ℕ → Fin r → ℝ) (s k : ℕ) : ℝ :=
  Matrix.det (fun i j => A (batchOmittedExponent r s k i) j)

/-- The consecutive-window Cauchy--Binet circuit block. -/
def batchCircuitBlock {r : ℕ} (A : ℕ → Fin r → ℝ) (y : Fin r → ℝ) (s : ℕ) : ℝ :=
  (Finset.range (r + 1)).sum (fun k =>
    Matrix.det (fun i j => y i ^ batchOmittedExponent r s k j) *
      batchWindowMinor A s k)

/-- Claim 18557: the consecutive-window Cauchy--Binet circuit identity. -/
def claim18557 : Prop :=
  ∀ {r : ℕ} (A : ℕ → Fin r → ℝ) (y : Fin r → ℝ) (s : ℕ),
    batchCircuitBlock A y s =
      batchVandermonde y * (∏ i : Fin r, y i) ^ s *
        (Finset.range (r + 1)).sum (fun k =>
          batchWindowMinor A s k * batchElementarySymmetric y k)

/-- The reciprocal two-sheet point kernel from Claims 18567--18568. -/
def reciprocalTwoSheetKernel (q u : ℝ) : ℝ :=
  Real.exp (-5 * u / 2 - q * Real.exp (-2 * u)) +
    Real.exp (5 * u / 2 - q * Real.exp (2 * u))

/-- The mixed logarithmic derivative of that kernel. -/
def reciprocalMixedLogDerivative (q u : ℝ) : ℝ :=
  deriv (fun q' : ℝ =>
    deriv (fun u' : ℝ => Real.log (reciprocalTwoSheetKernel q' u')) u) q

/-- Claim 18567: positivity of the reciprocal kernel's mixed logarithmic derivative. -/
def claim18567 : Prop :=
  ∀ (q u : ℝ), Real.pi ≤ q → 0 < u →
    0 < reciprocalMixedLogDerivative q u

/-- Claim 18568: global strict TP2 of the reciprocal two-sheet kernel. -/
def claim18568 : Prop :=
  ∀ (q₁ q₂ u₁ u₂ : ℝ),
    Real.pi ≤ q₁ → q₁ < q₂ → 0 ≤ u₁ → u₁ < u₂ →
      0 < reciprocalTwoSheetKernel q₁ u₁ * reciprocalTwoSheetKernel q₂ u₂ -
        reciprocalTwoSheetKernel q₁ u₂ * reciprocalTwoSheetKernel q₂ u₁

/-- The hyperbolic-cosine kernel from Claim 18570. -/
def hyperbolicCosineKernel (u z : ℝ) : ℝ := Real.cosh (u * z)

/-- Its mixed logarithmic derivative. -/
def hyperbolicCosineMixedLogDerivative (u z : ℝ) : ℝ :=
  deriv (fun u' : ℝ =>
    deriv (fun z' : ℝ => Real.log (hyperbolicCosineKernel u' z')) z) u

/-- Claim 18570: strict TP2, its mixed derivative formula, and boundary strictness. -/
def claim18570 : Prop :=
  (∀ (u z : ℝ), 0 < u → 0 < z →
    hyperbolicCosineMixedLogDerivative u z =
        Real.tanh (u * z) + (u * z) / Real.cosh (u * z) ^ 2 ∧
      0 < hyperbolicCosineMixedLogDerivative u z) ∧
  (∀ (u₁ u₂ z₁ z₂ : ℝ),
    0 < u₁ → u₁ < u₂ → 0 < z₁ → z₁ < z₂ →
      0 < hyperbolicCosineKernel u₁ z₁ * hyperbolicCosineKernel u₂ z₂ -
        hyperbolicCosineKernel u₁ z₂ * hyperbolicCosineKernel u₂ z₁) ∧
  (∀ (u₁ u₂ z₂ : ℝ),
    0 < u₁ → u₁ < u₂ → 0 < z₂ →
      0 < hyperbolicCosineKernel u₁ 0 * hyperbolicCosineKernel u₂ z₂ -
        hyperbolicCosineKernel u₁ z₂ * hyperbolicCosineKernel u₂ 0)

end

end MathlibPlus.Open.ResearchFormalizationBatch019ffedd
=======
open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalizationBatch

def graphXor {V : Type} (G H : SimpleGraph V) : SimpleGraph V :=
  SimpleGraph.fromRel (fun x y =>
    (G.Adj x y ∧ ¬ H.Adj x y) ∨ (H.Adj x y ∧ ¬ G.Adj x y))

def graphDifference {V : Type} (G H : SimpleGraph V) : SimpleGraph V :=
  SimpleGraph.fromRel (fun x y => G.Adj x y ∧ ¬ H.Adj x y)

def starAt {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) :
    SimpleGraph (Fin n) :=
  SimpleGraph.fromRel (fun x y => G.Adj x y ∧ (x = v ∨ y = v))

def isSpanning {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  G.support = Set.univ

noncomputable def isolateCount {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  n - Set.ncard G.support

noncomputable def supportOverlap {n : ℕ} (A B : SimpleGraph (Fin n)) : ℕ :=
  Set.ncard A.support + Set.ncard B.support - n

def hasIsolate {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ v, v ∉ G.support

def isMatchingGraph {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ v, (G.neighborSet v).ncard ≤ 1

noncomputable def claim21241 {n : ℕ} (A B : SimpleGraph (Fin n)) : Prop :=
  isolateCount A = n - Set.ncard A.support ∧
    isolateCount B = n - Set.ncard B.support ∧
    supportOverlap A B = Set.ncard A.support + Set.ncard B.support - n ∧
    hasIsolate A ∧ hasIsolate B ∧
    (isolateCount A ≥ 2 ∨ isolateCount B ≥ 2) ∧
    isSpanning (graphXor A B)

def claim21242 : Prop :=
  ∀ (n : ℕ) (A B : SimpleGraph (Fin n)),
    hasIsolate A →
    hasIsolate B →
    (isolateCount A ≥ 2 ∨ isolateCount B ≥ 2) →
    isSpanning (graphXor A B) →
    supportOverlap A B ≤ n - 3

def claim21243 : Prop :=
  ∀ (n : ℕ) (C : SimpleGraph (Fin n)) (u v w : Fin n),
    isSpanning C →
    u ≠ w →
    (Cᶜ).Adj u v →
    (Cᶜ).Adj v w →
    ∃ A B : SimpleGraph (Fin n),
      A = starAt C v ∧
        B = graphXor C A ∧
        u ∉ A.support ∧
        w ∉ A.support ∧
        v ∉ B.support ∧
        graphXor A B = C

def claim21244 : Prop :=
  ∀ (n : ℕ) (C M A B : SimpleGraph (Fin n)) (u v : Fin n),
    isMatchingGraph M →
    C = graphDifference (SimpleGraph.completeGraph (Fin n)) M →
    graphXor A B = C →
    u ∉ A.support →
    v ∉ B.support →
    u ≠ v ∧
      M.Adj u v ∧
      (∀ x, x ≠ u → x ≠ v → x ∈ A.support ∧ x ∈ B.support) ∧
      A.support = {x | x ≠ u} ∧
      B.support = {x | x ≠ v}

def claim21245 : Prop :=
  ∀ (n : ℕ) (C : SimpleGraph (Fin n)),
    isSpanning C →
    ((∃ A B : SimpleGraph (Fin n),
        hasIsolate A ∧
          hasIsolate B ∧
          (isolateCount A ≥ 2 ∨ isolateCount B ≥ 2) ∧
          graphXor A B = C) ↔
      ¬ isMatchingGraph Cᶜ)

abbrev MatchingEdge (n : ℕ) := {s : Finset (Fin n) // s.card = 2}

def matchingEdgeOf {n : ℕ} (G : SimpleGraph (Fin n)) (e : MatchingEdge n) : Prop :=
  ∀ ⦃x y : Fin n⦄, x ∈ e.1 → y ∈ e.1 → x ≠ y → G.Adj x y

def isEdgeMatching {n : ℕ} (M : Finset (MatchingEdge n)) : Prop :=
  ∀ ⦃e f : MatchingEdge n⦄,
    e ∈ M → f ∈ M → e ≠ f → Disjoint e.1 f.1

noncomputable def allMatchings (n : ℕ) : Finset (Finset (MatchingEdge n)) := by
  classical
  exact Finset.univ.filter (fun M => isEdgeMatching M)

noncomputable def matchingSign {n : ℕ} (G : SimpleGraph (Fin n))
    (M : Finset (MatchingEdge n)) : ℤ := by
  classical
  exact ∏ e ∈ M, if matchingEdgeOf G e then (-1 : ℤ) else 1

noncomputable def signedMatchingPolynomial {n : ℕ} (G : SimpleGraph (Fin n)) :
    Polynomial ℤ := by
  classical
  exact ∑ M ∈ allMatchings n,
    Polynomial.monomial M.card (matchingSign G M)

noncomputable def graphEdgeCount {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ := by
  classical
  exact (Finset.univ.filter (fun e : MatchingEdge n => matchingEdgeOf G e)).card

abbrev GraphAutomorphism {n : ℕ} (G : SimpleGraph (Fin n)) :=
  {σ : Equiv.Perm (Fin n) // ∀ x y, G.Adj (σ x) (σ y) ↔ G.Adj x y}

noncomputable def sigma {n : ℕ} (G : SimpleGraph (Fin n)) :
    Fin (n / 2 + 1) → ℚ := by
  classical
  exact fun q =>
    ((Nat.factorial n : ℚ) / (Fintype.card (GraphAutomorphism G) : ℚ)) *
      ((-1 : ℚ) ^ graphEdgeCount G) *
      ((signedMatchingPolynomial G).coeff q.1 : ℚ)

def claim21250 : Prop := by
  classical
  exact ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
    signedMatchingPolynomial G =
        (∑ M ∈ allMatchings n,
          Polynomial.monomial M.card (matchingSign G M)) ∧
      ∀ q : Fin (n / 2 + 1),
        sigma G q =
          ((Nat.factorial n : ℚ) /
              (Fintype.card (GraphAutomorphism G) : ℚ)) *
            ((-1 : ℚ) ^ graphEdgeCount G) *
            ((signedMatchingPolynomial G).coeff q.1 : ℚ)

def isPair {V : Type} (a b x y : V) : Prop :=
  (a = x ∧ b = y) ∨ (a = y ∧ b = x)

noncomputable def faceGraph {n : ℕ} (H : SimpleGraph (Fin n))
    (x u v : Fin n) (ε η : Bool) : SimpleGraph (Fin n) := by
  classical
  exact SimpleGraph.fromRel (fun a b =>
    if isPair a b x u then ε = true
    else if isPair a b x v then η = true
    else H.Adj a b)

def claim21253 : Prop :=
  ∀ (n : ℕ) (x u v : Fin n) (H : SimpleGraph (Fin n)),
    x ≠ u → x ≠ v → u ≠ v →
    (∑ ε : Bool, ∑ η : Bool, sigma (faceGraph H x u v ε η)) = 0

def unionProduct {α : Type} [DecidableEq α]
    (A B : Finset (Finset α)) : Finset (Finset α) :=
  A.biUnion (fun a : Finset α =>
    B.image (fun b : Finset α => (a ∪ b : Finset α)))

def claim21271 : Prop :=
  ∀ {α : Type} [DecidableEq α] (A B : Finset (Finset α)),
    unionProduct A B =
      A.biUnion (fun a : Finset α =>
        B.image (fun b : Finset α => (a ∪ b : Finset α)))

def unionClosed {α : Type} [DecidableEq α] (F : Finset (Finset α)) : Prop :=
  ∀ ⦃s t : Finset α⦄, s ∈ F → t ∈ F → s ∪ t ∈ F

def emptyTotalIntersection {α : Type} (F : Finset (Finset α)) : Prop :=
  ∀ x : α, ∃ s, s ∈ F ∧ x ∉ s

def hasFamilyBottom {α : Type} (F : Finset (Finset α)) : Prop :=
  ∃ s, s ∈ F ∧ ∀ t, t ∈ F → s ⊆ t

def claim21272 : Prop :=
  ∀ {α : Type} [DecidableEq α] (A B : Finset (Finset α)),
    A.Nonempty →
    B.Nonempty →
    unionClosed A →
    unionClosed B →
    (∅ : Finset α) ∉ A →
    (∅ : Finset α) ∉ B →
    emptyTotalIntersection A →
    emptyTotalIntersection B →
    (unionProduct A B).card = 7 →
    Nat.min A.card B.card ≤ 18

def claim21274 : Prop :=
  ∀ {α : Type} [DecidableEq α] (A B : Finset (Finset α)),
    (∅ : Finset α) ∉ A →
    (∅ : Finset α) ∉ B →
    emptyTotalIntersection A →
    emptyTotalIntersection B →
    emptyTotalIntersection (unionProduct A B) ∧
      (∀ s, s ∈ unionProduct A B → s.Nonempty) ∧
      ¬ hasFamilyBottom (unionProduct A B)

end MathlibPlus.Open.ResearchFormalizationBatch
>>>>>>> theirs
=======
open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalizationBatch019ffedd

noncomputable section

abbrev FiniteGraph := Sigma (fun n : Nat => SimpleGraph (Fin n))

def graphIsoRel (G H : FiniteGraph) : Prop := Nonempty (G.2.Adj ≃r H.2.Adj)

instance finiteGraphSetoid : Setoid FiniteGraph where
  r := graphIsoRel
  iseqv := {
    refl := fun G => ⟨RelIso.refl G.2.Adj⟩
    symm := fun h => h.map RelIso.symm
    trans := fun h₁ h₂ => by
      rcases h₁ with ⟨f⟩
      rcases h₂ with ⟨g⟩
      exact ⟨RelIso.trans f g⟩
  }

abbrev GraphIsoClass := Quotient finiteGraphSetoid

def graphClass (G : FiniteGraph) : GraphIsoClass := Quotient.mk _ G

def vertexCard : {n : Nat} → SimpleGraph (Fin n) → Fin n → FiniteGraph
  | 0, _, v => Fin.elim0 v
  | n + 1, g, v => ⟨n, g.comap (Fin.succAbove v)⟩

def edgeCard {n : Nat} (g : SimpleGraph (Fin n)) (e : Sym2 (Fin n)) : FiniteGraph :=
  ⟨n, g.deleteEdges {e}⟩

def incident {n : Nat} (v : Fin n) (e : Sym2 (Fin n)) : Prop :=
  ∃ w : Fin n, s(v, w) = e

def mixedCornerCard : {n : Nat} → SimpleGraph (Fin n) → Fin n → Sym2 (Fin n) → FiniteGraph
  | 0, _, v, _ => Fin.elim0 v
  | n + 1, g, v, e => ⟨n, (g.deleteEdges {e}).comap (Fin.succAbove v)⟩

def vertexDeck {n : Nat} (g : SimpleGraph (Fin n)) : Multiset GraphIsoClass :=
  (Finset.univ : Finset (Fin n)).val.map (fun v => graphClass (vertexCard g v))

def edgeDeck {n : Nat} (g : SimpleGraph (Fin n)) : Multiset GraphIsoClass := by
  letI : Fintype g.edgeSet := Fintype.ofFinite _
  exact g.edgeFinset.val.map (fun e => graphClass (edgeCard g e))

def mixedCornerDeck {n : Nat} (g : SimpleGraph (Fin n)) : Multiset GraphIsoClass := by
  classical
  letI : Fintype g.edgeSet := Fintype.ofFinite _
  exact g.edgeFinset.val.bind (fun e =>
    (Finset.univ.filter (fun v => ¬ incident v e)).val.map
      (fun v => graphClass (mixedCornerCard g v e)))

def trivialAutomorphism (G : FiniteGraph) : Prop :=
  ∀ φ : G.2.Adj ≃r G.2.Adj, φ = RelIso.refl G.2.Adj

def claim19889 : Prop :=
  ∀ {n : Nat} (g : SimpleGraph (Fin n)),
    mixedCornerDeck g =
      (Finset.univ : Finset (Fin n)).val.bind (fun v => edgeDeck (vertexCard g v).2)

def claim19891 : Prop := by
  classical
  exact ∀ (G H : FiniteGraph),
    vertexDeck G.2 = vertexDeck H.2 →
    edgeDeck G.2 = edgeDeck H.2 →
    ∀ v : Fin G.1, ∀ e : Sym2 (Fin G.1),
      e ∈ G.2.edgeSet →
      ¬ incident v e →
      let C := mixedCornerCard G.2 v e
      Multiset.count (graphClass C) (mixedCornerDeck G.2) = 1 →
      Multiset.count (graphClass C) (vertexDeck G.2) = 0 →
      trivialAutomorphism C →
      graphIsoRel G H

def claim19893 : Prop := by
  classical
  exact ∀ (G H : FiniteGraph),
    ¬ graphIsoRel G H →
    vertexDeck G.2 = vertexDeck H.2 →
    edgeDeck G.2 = edgeDeck H.2 →
    ∀ v : Fin G.1, ∀ e : Sym2 (Fin G.1),
      e ∈ G.2.edgeSet →
      ¬ incident v e →
      let C := mixedCornerCard G.2 v e
      Multiset.count (graphClass C) (mixedCornerDeck G.2) ≠ 1 ∨
      Multiset.count (graphClass C) (vertexDeck G.2) ≠ 0 ∨
      ¬ trivialAutomorphism C

def monomialSpanFamily (ell N : Nat) : Set (MvPolynomial (Fin 2) ℚ) :=
  {p | ∃ t : Fin (N + 1) → Nat,
    (∑ j : Fin (N + 1), t j) = ell ∧
    (∑ j : Fin (N + 1), (j : Nat) * t j) = N ∧
    p = ∏ j : Fin (N + 1),
      (1 + MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2) ^ (j : Nat)) ^ t j}

def monomialSpanDimension (ell N : Nat) : Nat :=
  Module.finrank ℚ (Submodule.span ℚ (monomialSpanFamily ell N))

def ceilHalf (n : Nat) : Nat := (n + 1) / 2

def allFactorFormula (ell N : Nat) : Nat :=
  1 +
      (∑ r : Fin (ceilHalf ell - 1), (N + 1 - 2 * ((r : Nat) + 1))) +
    if Even ell then ((N + 2) / 2 - ell / 2) else 0

def claim19814 : Prop :=
  ∀ ell N : Nat, 1 ≤ ell → monomialSpanDimension ell N = allFactorFormula ell N

end
end MathlibPlus.Open.ResearchFormalizationBatch019ffedd
>>>>>>> theirs
