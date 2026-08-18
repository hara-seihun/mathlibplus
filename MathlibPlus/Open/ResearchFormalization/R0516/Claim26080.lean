import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R0516.Claim26080

noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

inductive ResidualVar
  | xTwo
  | zTwo
  | y
  deriving DecidableEq

inductive TwoColorVar
  | xOne
  | xTwo
  | zOne
  | zTwo
  | y
  deriving DecidableEq

def graphEdgePredicate {V : Type*} [Fintype V]
    (T : SimpleGraph V) (e : Finset V) : Prop :=
  e.card = 2 ∧
    ∀ u ∈ e, ∀ v ∈ e, u ≠ v → T.Adj u v

noncomputable def graphEdgeFinset {V : Type*} [Fintype V]
    (T : SimpleGraph V) : Finset (Finset V) :=
  (Finset.univ : Finset (Finset V)).filter (graphEdgePredicate T)

def edgeMonochromatic {V : Type*} {q : ℕ}
    (c : V → Fin q) (e : Finset V) : Prop :=
  ∀ u ∈ e, ∀ v ∈ e, c u = c v

noncomputable def vertexColorCount
    {V : Type*} [Fintype V] {q : ℕ}
    (c : V → Fin q) (color : Fin q) : ℕ :=
  (Finset.univ.filter (fun v => c v = color)).card

noncomputable def monochromaticEdgeCount
    {V : Type*} [Fintype V] {q : ℕ}
    (T : SimpleGraph V) (c : V → Fin q) (color : Fin q) : ℕ :=
  (graphEdgeFinset T).filter
    (fun e => ∀ v ∈ e, c v = color) |>.card

noncomputable def unequalEdgeCount
    {V : Type*} [Fintype V] {q : ℕ}
    (T : SimpleGraph V) (c : V → Fin q) : ℕ :=
  (graphEdgeFinset T).filter (fun e => ¬ edgeMonochromatic c e) |>.card

noncomputable def residualExponent
    {V : Type*} [Fintype V]
    (T : SimpleGraph V) (c : V → Fin 3) : ResidualVar →₀ ℕ :=
  Finsupp.single ResidualVar.xTwo (vertexColorCount c 2) +
    Finsupp.single ResidualVar.zTwo
      (monochromaticEdgeCount T c 2) +
    Finsupp.single ResidualVar.y (unequalEdgeCount T c)

noncomputable def markedExponent
    {V : Type*} [Fintype V]
    (T : SimpleGraph V) (c : V → Fin 3) : TwoColorVar →₀ ℕ :=
  Finsupp.single TwoColorVar.xOne (vertexColorCount c 1) +
    Finsupp.single TwoColorVar.zOne
      (monochromaticEdgeCount T c 1) +
    Finsupp.single TwoColorVar.xTwo (vertexColorCount c 2) +
    Finsupp.single TwoColorVar.zTwo
      (monochromaticEdgeCount T c 2) +
    Finsupp.single TwoColorVar.y (unequalEdgeCount T c)

noncomputable def generalizedDegreeOne
    {V : Type*} [Fintype V] (T : SimpleGraph V) :
    MvPolynomial ResidualVar ℤ :=
  ∑ c : V → Fin 2,
    MvPolynomial.monomial
      (Finsupp.single ResidualVar.xTwo (vertexColorCount c 1) +
        Finsupp.single ResidualVar.zTwo
          (monochromaticEdgeCount T c 1) +
        Finsupp.single ResidualVar.y (unequalEdgeCount T c)) 1

noncomputable def generalizedDegreeTwo
    {V : Type*} [Fintype V] (T : SimpleGraph V) :
    MvPolynomial TwoColorVar ℤ :=
  ∑ c : V → Fin 3,
    MvPolynomial.monomial (markedExponent T c) 1

noncomputable def deletedGraph {V : Type*} [Fintype V]
    (T : SimpleGraph V) (S : Finset V) :
    SimpleGraph {v : V // v ∉ (S : Set V)} :=
  T.induce ((S : Set V)ᶜ)

noncomputable def generalizedDegreeOneOn
    {V : Type*} [Fintype V]
    (T : SimpleGraph V) (S : Finset V) :
    MvPolynomial ResidualVar ℤ :=
  generalizedDegreeOne (deletedGraph T S)

def boundaryEdge {V : Type*} [Fintype V]
    (S : Finset V) (e : Finset V) : Prop :=
  (∃ u ∈ e, u ∈ S) ∧ (∃ v ∈ e, v ∉ S)

noncomputable def boundaryCount {V : Type*} [Fintype V]
    (T : SimpleGraph V) (S : Finset V) : ℕ :=
  (graphEdgeFinset T).filter (boundaryEdge S) |>.card

def selectedSupportConnected {V : Type*} [Fintype V]
    (T : SimpleGraph V) (S : Finset V) : Prop :=
  (T.induce (S : Set V)).Connected

noncomputable def connectedDeletionLayer
    {V : Type*} [Fintype V]
    (T : SimpleGraph V) (k : ℕ) :
    MvPolynomial ResidualVar ℤ :=
  ∑ S : Finset V,
    if S.card = k ∧ selectedSupportConnected T S then
      (MvPolynomial.X ResidualVar.y : MvPolynomial ResidualVar ℤ) ^
          boundaryCount T S * generalizedDegreeOneOn T S
    else 0

noncomputable def residualExponentOfMarked
    (m : TwoColorVar →₀ ℕ) : ResidualVar →₀ ℕ :=
  Finsupp.single ResidualVar.xTwo (m TwoColorVar.xTwo) +
    Finsupp.single ResidualVar.zTwo (m TwoColorVar.zTwo) +
    Finsupp.single ResidualVar.y (m TwoColorVar.y)

/-- The actual coefficient of `x₁^k z₁^(k-1)` in `G^(2)`, retaining the
remaining `x₂,z₂,y` variables. -/
noncomputable def markedCoefficient
    {V : Type*} [Fintype V]
    (T : SimpleGraph V) (k : ℕ) : MvPolynomial ResidualVar ℤ :=
  (generalizedDegreeTwo T).support.filter
      (fun m => m TwoColorVar.xOne = k ∧
        m TwoColorVar.zOne = k - 1) |>.sum
    (fun m =>
      MvPolynomial.monomial (residualExponentOfMarked m)
        ((generalizedDegreeTwo T).coeff m))

/-- Claim 26080: the actual marked coefficient of `G_T^(2)` equals the
weighted connected-subtree deletion layer `𝓛_k(T)`. -/
def claim26080_connectedCoefficientIdentity : Prop :=
  ∀ {V : Type*} [Fintype V]
    (T : SimpleGraph V) (k : ℕ),
    T.IsTree → 1 ≤ k →
      markedCoefficient T k = connectedDeletionLayer T k

end

end MathlibPlus.Open.ResearchFormalization.R0516.Claim26080
