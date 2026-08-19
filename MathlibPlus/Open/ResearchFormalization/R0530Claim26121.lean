import MathlibPlus.Open.ResearchFormalizationBatch019ffedf141b77c7b96e46e312eadae9

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R0530Claim26121

open MathlibPlus.Open.ResearchFormalizationBatch

noncomputable section

structure LegFamily where
  count : ℕ
  length : Fin count → ℕ

private def positiveLegFamily (A : LegFamily) : Prop :=
  ∀ i, 0 < A.length i

private def legSum (A : LegFamily) : ℕ :=
  ∑ i : Fin A.count, A.length i

structure DoubleSpider where
  smaller : LegFamily
  trunk : ℕ
  larger : LegFamily

private def validDoubleSpider (T : DoubleSpider) : Prop :=
  positiveLegFamily T.smaller ∧
    positiveLegFamily T.larger ∧
    2 ≤ T.smaller.count ∧ 2 ≤ T.larger.count ∧ 1 ≤ T.trunk

private abbrev LegVertex (A : LegFamily) :=
  Σ i : Fin A.count, Fin (A.length i)

private def legAdjacent {A : LegFamily}
    (x y : LegVertex A) : Prop :=
  x.1 = y.1 ∧
    (x.2.val + 1 = y.2.val ∨ y.2.val + 1 = x.2.val)

private abbrev SpiderVertex (A B : LegFamily) (c : ℕ) :=
  Fin (c + 1) ⊕ (LegVertex A ⊕ LegVertex B)

private def doubleSpiderRelation (A B : LegFamily) (c : ℕ)
    (u v : SpiderVertex A B c) : Prop :=
  match u, v with
  | Sum.inl r, Sum.inl s => r.val + 1 = s.val
  | Sum.inl r, Sum.inr (Sum.inl x) => r.val = 0 ∧ x.2.val = 0
  | Sum.inr (Sum.inl x), Sum.inl r => r.val = 0 ∧ x.2.val = 0
  | Sum.inl r, Sum.inr (Sum.inr x) => r.val = c ∧ x.2.val = 0
  | Sum.inr (Sum.inr x), Sum.inl r => r.val = c ∧ x.2.val = 0
  | Sum.inr (Sum.inl x), Sum.inr (Sum.inl y) => legAdjacent x y
  | Sum.inr (Sum.inr x), Sum.inr (Sum.inr y) => legAdjacent x y
  | _, _ => False

private def doubleSpiderGraph (A B : LegFamily) (c : ℕ) :
    SimpleGraph (SpiderVertex A B c) :=
  SimpleGraph.fromRel (doubleSpiderRelation A B c)

private noncomputable def spiderU {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : MvPolynomial ℕ ℚ :=
  unsignedConnectedSetPolynomial G

private noncomputable def doubleU (T : DoubleSpider) : MvPolynomial ℕ ℚ :=
  spiderU (doubleSpiderGraph T.smaller T.larger T.trunk)

private noncomputable def pathGraph (n : ℕ) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel (fun u v : Fin n => u.val + 1 = v.val)

private noncomputable def pathU (n : ℕ) : MvPolynomial ℕ ℚ :=
  spiderU (pathGraph n)

private def rootSideRelation (A : LegFamily) (i : ℕ)
    (u v : Fin (i + 1) ⊕ LegVertex A) : Prop :=
  match u, v with
  | Sum.inl r, Sum.inl s => r.val + 1 = s.val
  | Sum.inl r, Sum.inr x => r.val = 0 ∧ x.2.val = 0
  | Sum.inr x, Sum.inl r => r.val = 0 ∧ x.2.val = 0
  | Sum.inr x, Sum.inr y => legAdjacent x y

private noncomputable def rootSideGraph (A : LegFamily) (i : ℕ) :
    SimpleGraph (Fin (i + 1) ⊕ LegVertex A) :=
  SimpleGraph.fromRel (rootSideRelation A i)

private noncomputable def rootSideU (A : LegFamily) (i : ℕ) : MvPolynomial ℕ ℚ :=
  spiderU (rootSideGraph A i)

private noncomputable def trunkEdges (T : DoubleSpider) :
    Finset (Sym2 (SpiderVertex T.smaller T.larger T.trunk)) :=
  (Finset.univ : Finset (Fin T.trunk)).image (fun i =>
    s((Sum.inl (Fin.castSucc i) : SpiderVertex T.smaller T.larger T.trunk),
      (Sum.inl (Fin.succ i) : SpiderVertex T.smaller T.larger T.trunk)))

private noncomputable def noTrunkCutU (T : DoubleSpider) :
    MvPolynomial ℕ ℚ :=
  let G := doubleSpiderGraph T.smaller T.larger T.trunk
  letI : Fintype G.edgeSet := Fintype.ofFinite _
  ∑ E₀ ∈ G.edgeFinset.powerset,
    if trunkEdges T ⊆ E₀ then componentMonomial E₀ else 0

private noncomputable def crossedU (T : DoubleSpider) : MvPolynomial ℕ ℚ :=
  doubleU T - noTrunkCutU T

private noncomputable def crossedM (T : DoubleSpider) : MvPolynomial ℕ ℚ :=
  partialOne (crossedU T)

private noncomputable def crossedFactorizedU (T : DoubleSpider) :
    MvPolynomial ℕ ℚ :=
  ∑ i ∈ Finset.range T.trunk,
    ∑ j ∈ Finset.range T.trunk,
      ∑ h ∈ Finset.range T.trunk,
        if i + j + h = T.trunk - 1 then
          rootSideU T.smaller i * pathU h * rootSideU T.larger j
        else 0

/-- The no-trunk-cut subtraction agrees with the exact corridor convolution,
and singleton marking is the `x₁` partial derivative of the crossed sector. -/
def crossedTrunkCorridorFactorization_claim26121 : Prop :=
  ∀ T : DoubleSpider,
    validDoubleSpider T →
      crossedU T = crossedFactorizedU T ∧
        crossedM T = partialOne (crossedU T)

end

end MathlibPlus.Open.ResearchFormalization.R0530Claim26121
