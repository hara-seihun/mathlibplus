import MathlibPlus.Open.Research.FormalizationBatchUPolynomial

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R1724

attribute [local instance] Classical.decEq Classical.propDecidable

noncomputable section

private abbrev XPoly := MvPolynomial ℕ ℚ
private abbrev WPoly := Polynomial XPoly

private structure RootedTree where
  carrier : Type
  fintype : Fintype carrier
  graph : SimpleGraph carrier
  root : carrier
  isTree : graph.IsTree

private def treeOrder (T : RootedTree) : ℕ :=
  @Fintype.card T.carrier T.fintype

private def connectedBlock {V : Type*} [Fintype V]
    (G : SimpleGraph V) (D : Finset V) : Prop :=
  D.Nonempty ∧ (G.induce (D : Set V)).Connected

private def connectedPartition {V : Type*} [Fintype V]
    (G : SimpleGraph V) (S : Finset V) (π : Finset (Finset V)) : Prop :=
  π.biUnion id = S ∧
    (∀ D ∈ π, D.Nonempty ∧ D ⊆ S ∧ connectedBlock G D) ∧
    (∀ D ∈ π, ∀ E ∈ π, D ≠ E → Disjoint D E)

private def rootConnectedSet (T : RootedTree) (Q : Finset T.carrier) : Prop :=
  Q = ∅ ∨ (T.root ∈ Q ∧ (T.graph.induce (Q : Set T.carrier)).Connected)

private def blockMonomial {V : Type*}
    (π : Finset (Finset V)) : XPoly :=
  ∏ D ∈ π, MvPolynomial.X D.card

private noncomputable def pruningFactor (T : RootedTree) : WPoly := by
  classical
  letI := T.fintype
  exact ∑ Q : Finset T.carrier, ∑ π : Finset (Finset T.carrier),
    if rootConnectedSet T Q ∧ connectedPartition T.graph Qᶜ π then
      Polynomial.X ^ (treeOrder T - Q.card) * Polynomial.C (blockMonomial π)
    else 0

private def pruningProduct (C : Multiset RootedTree) : WPoly :=
  (C.map pruningFactor).prod

private def row (k : ℕ) (C : Multiset RootedTree) : XPoly :=
  (pruningProduct C).coeff k

private def markedRow (k : ℕ) (C : Multiset RootedTree) : XPoly :=
  MvPolynomial.pderiv 1 (row k C)

private def totalWeight (C : Multiset RootedTree) : ℕ :=
  (C.map treeOrder).sum

private def rowDifference (k : ℕ) (A B : Multiset RootedTree) : XPoly :=
  row k A - row k B

private def exactDepthCapPair (d : ℕ) (A B : Multiset RootedTree) : Prop :=
  totalWeight A = totalWeight B ∧
    (∀ k, k < d → row k A = row k B) ∧
    markedRow d A = markedRow d B ∧ row d A ≠ row d B

private def xOneFree (P : XPoly) : Prop :=
  MvPolynomial.pderiv 1 P = 0

private noncomputable def capSpace (d : ℕ) : Submodule ℚ XPoly :=
  Submodule.span ℚ {f | ∃ A B : Multiset RootedTree,
    exactDepthCapPair d A B ∧ f = rowDifference d A B}

private noncomputable def uPoly {d : ℕ} (T : SimpleGraph (Fin d)) : XPoly := by
  classical
  letI : Fintype (T.edgeSet) := Fintype.ofFinite _
  exact MvPolynomial.map (Int.castRingHom ℚ)
    (MathlibPlus.Open.ResearchFormalizationBatch.forestUPolynomial T)

private noncomputable def treeCsf {d : ℕ} (T : SimpleGraph (Fin d)) : XPoly := by
  classical
  exact ∑ A : Finset (Sym2 (Fin d)),
    if (∀ e ∈ A, e ∈ T.edgeSet) then
      ((-1 : ℚ) ^ A.card) •
        MvPolynomial.map (Int.castRingHom ℚ)
          (∏ C ∈ MathlibPlus.Open.ResearchFormalizationBatch.uComponents A,
            MvPolynomial.X C.card)
    else 0

private noncomputable def treeSetSpan (d : ℕ) : Submodule ℚ XPoly :=
  Submodule.span ℚ {f | ∃ T : SimpleGraph (Fin d), T.IsTree ∧ f = uPoly T}

private noncomputable def treeCsfSpan (d : ℕ) : Submodule ℚ XPoly :=
  Submodule.span ℚ {f | ∃ T : SimpleGraph (Fin d), T.IsTree ∧ f = treeCsf T}

private noncomputable def topUFreeSpace (d : ℕ) : Submodule ℚ XPoly :=
  Submodule.span ℚ {f | ∃ ν : SimpleGraph (Fin d) →₀ ℚ,
    (∀ T, ν T ≠ 0 → T.IsTree) ∧
    f = ∑ T ∈ ν.support, (ν T) • uPoly T ∧
    xOneFree f}

private noncomputable def topCsfFreeSpace (d : ℕ) : Submodule ℚ XPoly :=
  Submodule.span ℚ {f | ∃ ν : SimpleGraph (Fin d) →₀ ℚ,
    (∀ T, ν T ≠ 0 → T.IsTree) ∧
    f = ∑ T ∈ ν.support, (ν T) • treeCsf T ∧
    xOneFree f}

private noncomputable def negVariableSubstitution : XPoly →+* XPoly :=
  MvPolynomial.eval₂Hom (MvPolynomial.C : ℚ →+* XPoly)
    (fun j => -MvPolynomial.X j)

private noncomputable def noOnePartitionNumber (d : ℕ) : ℕ :=
  Fintype.card {p : Nat.Partition d // 1 ∉ p.parts}

private def topRankTarget (d : ℕ) : ℕ :=
  noOnePartitionNumber d - d / 2

/-- Claim 33746: exact top-stratum and verified arbitrary-cap dimensions. -/
def topStratumCapDimension_claim33746 : Prop :=
  (∀ d, 2 ≤ d → d ≤ 16 →
    Module.finrank ℚ (topUFreeSpace d) = topRankTarget d) ∧
    Module.finrank ℚ (topUFreeSpace 4) = 0 ∧
    Module.finrank ℚ (topUFreeSpace 5) = 0 ∧
    Module.finrank ℚ (topUFreeSpace 6) = 1 ∧
    Module.finrank ℚ (topUFreeSpace 7) = 1 ∧
    Module.finrank ℚ (topUFreeSpace 8) = 3 ∧
    Module.finrank ℚ (topUFreeSpace 9) = 4 ∧
    Module.finrank ℚ (topUFreeSpace 10) = 7 ∧
    Module.finrank ℚ (topUFreeSpace 11) = 9 ∧
    Module.finrank ℚ (topUFreeSpace 12) = 15 ∧
    Module.finrank ℚ (topUFreeSpace 13) = 18 ∧
    Module.finrank ℚ (topUFreeSpace 14) = 27 ∧
    Module.finrank ℚ (topUFreeSpace 15) = 34 ∧
    Module.finrank ℚ (topUFreeSpace 16) = 47 ∧
    (∀ d, 4 ≤ d → d ≤ 11 →
      Module.finrank ℚ (capSpace d) = Module.finrank ℚ (topUFreeSpace d))

/-- Claim 33747: diagonal tree-CSF substitution and cap-space correspondence. -/
def treeCsfSubstitution_claim33747 : Prop :=
  (∀ {d : ℕ} (T : SimpleGraph (Fin d)), T.IsTree →
    treeCsf T = ((-1 : ℚ) ^ d) • negVariableSubstitution (uPoly T)) ∧
    Function.Bijective negVariableSubstitution ∧
    (∀ m : ℕ →₀ ℕ,
      negVariableSubstitution (MvPolynomial.monomial m 1) =
        ((-1 : ℚ) ^ m.sum (fun _ e => e)) •
          MvPolynomial.monomial m 1) ∧
    (∀ P : XPoly,
      xOneFree P ↔ xOneFree (negVariableSubstitution P)) ∧
    (∀ d, Nonempty (topUFreeSpace d ≃ₗ[ℚ] topCsfFreeSpace d))

end

end MathlibPlus.Open.ResearchFormalization.R1724
